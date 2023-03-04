//  The ID of a string.

use core::{
    fmt,
    num::NonZeroU32,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::error::InternerError;

/// A `Id` uniquely identifies a `Interner`, unless `new_unchecked` is used to create it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Id(NonZeroU32);

impl Id {
    /// The maximum value of the `Id`.
    pub const MAX_ID: u32 = (1u32 << INTERNER_BITS) - 1;

    /// Creates a new instance, with a guaranteed fresh new ID.
    ///
    /// Only 2^24 - 1 instances can be created by this method during the lifetime of the process, after which it fails
    /// unconditionally.
    pub fn new() -> Result<Self, InternerError> {
        static ID_POOL: AtomicU32 = AtomicU32::new(0);

        debug_assert!(Self::MAX_ID > 0);
        debug_assert!(Self::MAX_ID < u32::MAX);

        let mut current = ID_POOL.load(Ordering::Relaxed);

        loop {
            if current > Self::MAX_ID - 1 {
                return Err(InternerError::IdPoolExhausted);
            }

            let result = ID_POOL.compare_exchange_weak(
                current,
                current + 1,
                Ordering::Relaxed,
                Ordering::Relaxed,
            );

            if let Err(new_current) = result {
                current = new_current;
                continue;
            }

            //  Safety:
            //  -   `current + 1 > 0`.
            let id = unsafe { NonZeroU32::new_unchecked(current + 1) };

            return Ok(Self(id));
        }
    }

    /// Creates a new instance with the specified ID.
    ///
    /// This instance can then be used to create a `Interner` using its `new_unchecked` method, at the risk and
    /// perils of the caller.
    ///
    /// #   Panics.
    ///
    /// If the value is not less than `MAX_ID`.
    pub fn new_unchecked(n: NonZeroU32) -> Self {
        assert!(n.get() < Self::MAX_ID);

        Self(n)
    }
}

/// A `BytesId` uniquely identifies an interned slice of bytes.
///
/// #   Tied to the `Interner` instance.
///
/// A `BytesId` is only meaningful for the `Interner` instance which created it.
///
/// Both can be queried for the `Id` of the `Interner` in case of doubt.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct BytesId {
    offset: Offset,
    shard_interner: NonZeroU32,
}

//  Public methods
impl BytesId {
    /// Returns the `Id` of the `Interner` which created this instance.
    pub fn interner_id(&self) -> Id {
        let interner = self.shard_interner.get() >> SHARD_BITS;

        //  Safety:
        //  -   `self.shard_interner = Id << SHARD_BITS + ShardIndex`, so the recovered value must be non-0.
        let id = unsafe { NonZeroU32::new_unchecked(interner) };

        Id(id)
    }
}

//  Crate methods
impl BytesId {
    /// Creates a new instance.
    pub(crate) fn new(offset: Offset, interner: Id, shard: ShardIndex) -> Self {
        assert_eq!(32, INTERNER_BITS + SHARD_BITS);

        debug_assert!(interner.0.get() < (1u32 << INTERNER_BITS));

        let shard_interner = shard.0 as u32 | (interner.0.get() << SHARD_BITS);

        //  Safety:
        //  -   `interner.0 > 0` thus `shard.0 | interner.0 > 0`.
        let shard_interner = unsafe { NonZeroU32::new_unchecked(shard_interner) };

        Self {
            offset,
            shard_interner,
        }
    }

    /// Returns the offset of the bytes' slice within the `Interner`.
    pub(crate) fn offset(&self) -> Offset {
        self.offset
    }

    /// Returns the index of the `Shard` within the `Interner`.
    pub(crate) fn shard(&self) -> ShardIndex {
        let shard = self.shard_interner.get() as u8;

        ShardIndex(shard)
    }
}

impl fmt::Debug for BytesId {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let (interner, shard) = (self.interner_id(), self.shard());

        f.debug_struct("BytesId")
            .field("offset", &self.offset.0)
            .field("interner", &interner.0)
            .field("shard", &shard.0)
            .finish()
    }
}

/// A `StringId` uniquely identifies an interned string.
///
/// #   Tied to the `Interner` instance.
///
/// A `StringId` is only meaningful for the `Interner` instance which created it.
///
/// Both can be queried for the `Id` of the `Interner` in case of doubt.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct StringId(BytesId);

//  Public methods
impl StringId {
    /// Creates an instance from a BytesId.
    ///
    /// #   Safety
    ///
    /// The BytesId must point to a proper UTF-8 encoded slice of bytes.
    pub unsafe fn from_bytes_id(id: BytesId) -> Self {
        Self(id)
    }

    /// Returns the `Id` of the `Interner` which created this instance.
    pub fn interner_id(&self) -> Id {
        self.0.interner_id()
    }

    /// Returns as `BytesId`.
    pub fn as_bytes_id(&self) -> BytesId {
        self.0
    }
}

impl fmt::Debug for StringId {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let (interner, shard) = (self.interner_id(), self.0.shard());

        f.debug_struct("StringId")
            .field("offset", &self.0.offset.0)
            .field("interner", &interner.0)
            .field("shard", &shard.0)
            .finish()
    }
}

/// The offset of a byte slice or string within the `Interner`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Offset(pub NonZeroU32);

/// The index of a `Shard`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ShardIndex(pub u8);

//
//  Implementation
//

const INTERNER_BITS: u32 = 24;
const SHARD_BITS: u32 = 8;
