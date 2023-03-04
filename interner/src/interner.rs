//  Implementation of the `Interner`.

use core::{
    fmt,
    hash::{BuildHasher, Hasher},
    mem,
    ptr::{self, NonNull},
    sync::atomic::{AtomicU64, Ordering},
};

use alloc::alloc::{Allocator, Global, Layout};

use crate::{
    error::InternerError,
    hash::DefaultFxBuildHasher,
    id::{BytesId, Id, ShardIndex, StringId},
    shard::{Shard, ShardDirector},
};

/// A byte slice and string interner.
///
/// The Interner is designed for maximum wait-freedom in the face of parallel insertions, while still being safe to use.
pub struct Interner<H = DefaultFxBuildHasher, A = Global>(NonNull<InternerHeader<H, A>>)
where
    A: Allocator;

impl<H, A> Interner<H, A>
where
    A: Allocator,
{
    /// Creates a new Interner, with default configuration.
    ///
    /// This may fail either because the pool of IDs is exhausted, or because the allocator cannot currently allocate
    /// enough memory for the Interner.
    ///
    /// To customize the Interner, use the `with()` method instead.
    pub fn new() -> Result<Self, InternerError>
    where
        H: Default,
        A: Default,
    {
        Self::with(H::default(), A::default()).build()
    }

    /// Creates a builder for the Interner, allowing finer-grained tuning.
    pub fn with(hasher: H, allocator: A) -> InternerBuilder<H, A> {
        let id = None;
        let log_number_shards = 4; //  16 shards by default.
        let log_initial_bytes = 10; //  1024 bytes by default.
        let log_initial_groups = 3; //  128 entries by default.

        InternerBuilder {
            id,
            hasher,
            log_number_shards,
            log_initial_bytes,
            log_initial_groups,
            allocator,
        }
    }

    /// Gets a previous inserted bytes slice.
    ///
    /// Returns an error if the `id` is NOT for this instance.
    pub fn get_bytes(&self, id: BytesId) -> Result<&[u8], InternerError> {
        let header = self.get_header();

        if header.id != id.interner_id() {
            return Err(InternerError::IdMismatch);
        }

        let (shard, offset) = (id.shard(), id.offset());

        //  Safety:
        //  -   `shard` is derived from a matching `id`, so is within bounds.
        let shard = unsafe { self.get_shard(shard) };

        //  Safety:
        //  -   `offset` is derived from a matching `id`, and the appropriate `shard` was selected, thus `offset` was
        //      obtained from this `shard`.
        //  -   `shard` has not been reset since, has it takes dropping `self` to reset it.
        let bytes = unsafe { shard.get_unchecked(offset, &header.director) };

        Ok(bytes)
    }

    /// Gets a previous inserted string.
    ///
    /// Returns an error if the `id` is NOT for this instance.
    pub fn get_str(&self, id: StringId) -> Result<&str, InternerError> {
        let bytes = self.get_bytes(id.as_bytes_id())?;

        //  Safety:
        //  -   A `StringId` can only be obtained for valid `str`, so `bytes` contains a valid UTF-8 encoded string.
        let string = unsafe { core::str::from_utf8_unchecked(bytes) };

        Ok(string)
    }
}

impl<H, A> Interner<H, A>
where
    H: BuildHasher,
    A: Allocator,
{
    /// Inserts a slice of bytes.
    ///
    /// Returns the `BytesId` which can be used to retrieve this slice, or an error if insertion fails.
    pub fn insert_bytes(&self, bytes: &[u8]) -> Result<BytesId, InternerError> {
        let header = self.get_header();

        let hash = {
            let mut hasher = header.hasher.build_hasher();

            hasher.write(bytes);

            hasher.finish()
        };

        let (shard, _, _) = header.director.split_hash(hash);

        let offset = {
            //  Safety:
            //  -   `shard` is obtained from the `director`, so is within bounds.
            let shard = unsafe { self.get_shard(shard) };

            //  Safety:
            //  -   This `director` is used for all insertions in `shard`.
            unsafe { shard.insert(hash, bytes, &header.director)? }
        };

        Ok(BytesId::new(offset, header.id, shard))
    }

    /// Inserts a string.
    ///
    /// Returns the `StringId` which can be used to retrieve this string, or an error if insertion fails.
    pub fn insert_string(&self, string: &str) -> Result<StringId, InternerError> {
        let bytes = self.insert_bytes(string.as_bytes())?;

        //  Safety:
        //  -   A string was inserted.
        let result = unsafe { StringId::from_bytes_id(bytes) };

        Ok(result)
    }

    //  TODO: statistics.
}

impl<H, A> Clone for Interner<H, A>
where
    A: Allocator,
{
    fn clone(&self) -> Self {
        let header = self.get_header();

        header.ref_count.fetch_add(1, Ordering::Relaxed);

        Self(self.0)
    }
}

impl<H, A> Drop for Interner<H, A>
where
    A: Allocator,
{
    fn drop(&mut self) {
        let header = self.get_header();

        let previous = header.ref_count.fetch_sub(1, Ordering::Relaxed);

        if previous > 1 {
            return;
        }

        let number_shards = header.director.number_shards();

        for shard in 0..number_shards {
            let shard = ShardIndex(shard as u8);

            //  Safety:
            //  -   `shard` is within bounds.
            let shard = unsafe { self.get_shard(shard) };

            //  Safety:
            //  -   The same director was used for all operations.
            unsafe { shard.reset(&header.director) }
        }

        let layout = Self::layout(number_shards.ilog2() as u8);

        //  Safety:
        //  -   No further call to `into_allocator` will occur.
        let allocator = unsafe { header.director.into_allocator() };

        //  Safety:
        //  -   `self.0` will no longer be used: this was the last reference, and this is the last line.
        //  -   `self.0` was allocated by this allocator.
        //  -   `layout` was calculated the same way as for the allocation of `self.0`.
        unsafe { allocator.deallocate(self.0.cast(), layout) }
    }
}

impl<H, A> fmt::Debug for Interner<H, A>
where
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let header = self.get_header();

        write!(f, "{{ header: {header:?}, shards: [")?;

        for (index, shard) in self.get_shards().iter().enumerate() {
            let separator = if index > 0 { ", " } else { "" };

            write!(f, "{separator}[")?;

            //  Safety:
            //  -   `header.director` has been used for all insertions in `shard`.
            let iterator = unsafe { shard.iter_with_metadata(&header.director) };

            for (index, (slice, store, set)) in iterator.enumerate() {
                let separator = if index > 0 { ", " } else { "" };

                write!(
                    f,
                    "{separator}({:?}, {}, {}) -> ({:?}, {}) -> ",
                    set.part, set.group, set.index, store.part, store.offset,
                )?;

                if let Ok(string) = core::str::from_utf8(slice) {
                    write!(f, "{string:?}")?;
                } else {
                    write!(f, "{slice:x?}")?;
                }
            }

            write!(f, "]")?;
        }

        write!(f, "] }}")
    }
}

//  Safety:
//  -   The Interner itself is Send, using an `Atomic` for reference-counting, and Send parts.
unsafe impl<H, A> Send for Interner<H, A>
where
    H: Send,
    A: Allocator + Send,
{
}

//  Safety:
//  -   The Interner itself is Sync, using an `Atomic` for reference-counting, and Sync parts.
unsafe impl<H, A> Sync for Interner<H, A>
where
    H: Sync,
    A: Allocator + Sync,
{
}

/// A builder for the Interner.
pub struct InternerBuilder<H, A> {
    id: Option<Id>,
    hasher: H,
    log_number_shards: u8,
    log_initial_bytes: u8,
    log_initial_groups: u8,
    allocator: A,
}

impl<H, A> InternerBuilder<H, A> {
    /// Sets the ID with which to build the Interner.
    ///
    /// #   Safety
    ///
    /// The ID is used to tie a `BytesId` or `StringId` to its matching `Interner`, the user should ensure that no
    /// `BytesId` or `StringId` with this `id` from another `Interner` are ever used with this instance.
    pub unsafe fn set_id(&mut self, id: Id) -> &mut Self {
        self.id = Some(id);
        self
    }

    /// Sets the number of shards.
    ///
    /// It is recommended to use roughly 2x the number of logical cores, to minimize contention.
    ///
    /// #   Panics
    ///
    /// If `number_shards` is not a power of 2.
    pub fn set_number_shards(&mut self, number_shards: u8) -> &mut Self {
        assert_eq!(1, number_shards.count_ones());

        self.log_number_shards = number_shards.ilog2() as u8;
        self
    }

    /// Sets the number of bytes of the initial jagged part of the bytes vector.
    ///
    /// The total capacity of a single shard will be equal to 32K the initial specified capacity.
    ///
    /// #   Panics
    ///
    /// If `number_bytes` is not a power of 2, or is less than 8.
    pub fn set_number_bytes(&mut self, number_bytes: usize) -> &mut Self {
        assert_eq!(1, number_bytes.count_ones());
        assert!(number_bytes >= 8);

        self.log_initial_bytes = number_bytes.ilog2() as u8;
        self
    }

    /// Sets the number of entries of the initial jagged part of the hash set.
    ///
    /// The total capacity of a single shard will be equal to 32K the initial specified capacity.
    ///
    /// #   Panics
    ///
    /// If `number_entries` is not a power of 2, or is less than 128.
    pub fn set_number_entries(&mut self, number_entries: usize) -> &mut Self {
        assert_eq!(1, number_entries.count_ones());
        assert!(number_entries >= 128);

        self.log_initial_groups = (number_entries / 16).ilog2() as u8;
        self
    }
}

impl<H, A> InternerBuilder<H, A>
where
    A: Allocator,
{
    /// Attempts to build an Interner with the current configuration.
    ///
    /// This may fail either because:
    ///
    /// -   No ID was specified, and the pool of IDs is exhausted,
    //  -   or because the allocator cannot currently allocate enough memory for the Interner itself.
    pub fn build(self) -> Result<Interner<H, A>, InternerError> {
        let id = if let Some(id) = self.id {
            id
        } else {
            Id::new()?
        };

        let hasher = self.hasher;

        let director = ShardDirector::new(
            self.log_number_shards,
            self.log_initial_bytes,
            self.log_number_shards,
            self.allocator,
        );

        Interner::allocate(id, hasher, director)
    }
}

//
//  Implementation
//

#[repr(align(16))]
struct InternerHeader<H, A> {
    ref_count: AtomicU64, //  Number of owners - 1.
    id: Id,
    hasher: H,
    director: ShardDirector<A>,
}

impl<H, A> Interner<H, A>
where
    A: Allocator,
{
    fn layout(log_number_shards: u8) -> Layout {
        let number_shards = 1usize << log_number_shards;

        let header_layout = Layout::new::<InternerHeader<H, A>>();
        let shards_layout =
            Layout::array::<Shard>(number_shards).expect("Sufficiently low number of shards");

        let (layout, offset) = header_layout
            .extend(shards_layout)
            .expect("Sufficiently low number of shards");
        assert_eq!(0, offset);

        layout
    }

    fn allocate(id: Id, hasher: H, director: ShardDirector<A>) -> Result<Self, InternerError> {
        let layout = Self::layout(director.number_shards() as u8);

        let memory = director
            .allocator()
            .allocate_zeroed(layout)
            .map_err(|_| InternerError::MemoryExhausted)?;

        let header = memory.as_ptr();

        //  Safety:
        //  -   `header` is valid for writes, it's just freshly allocated.
        //  -   `header` is aligned for the exact layout of `InternerHeader`.
        unsafe { ptr::write(header as *mut _, InternerHeader::new(id, hasher, director)) };

        //  Shards default initialize to 0, so all good.

        Ok(Self(memory.as_non_null_ptr().cast()))
    }

    fn get_header(&self) -> &InternerHeader<H, A> {
        //  Safety:
        //  -   The pointer is properly aligned, or the allocator failed us.
        //  -   The pointer is dereferenceable.
        //  -   The pointer points to an initialized instance.
        //  -   The lifetime is tied to the lifetime of `self`, preventing the memory from being deallocated, or
        //      borrowed mutably.
        unsafe { self.0.as_ref() }
    }

    //  Returns a reference to the specified shard.
    //
    //  #   Safety
    //
    //  -   `index.0` must be less than the number of shards.
    unsafe fn get_shard(&self, index: ShardIndex) -> &Shard {
        let shards = self.get_shards();

        debug_assert!((index.0 as usize) < shards.len());

        //  Safety:
        //  -   `index.0` is within bounds.
        unsafe { shards.get_unchecked(index.0 as usize) }
    }

    //  Returns a reference to the slice of shards.
    fn get_shards(&self) -> &[Shard] {
        let header = self.get_header();

        let offset = mem::size_of::<InternerHeader<H, A>>();
        let number_shards = header.director.number_shards();

        let pointer: *mut u8 = self.0.cast().as_ptr();

        //  Safety:
        //  -   `offset` is within bounds, even with 0 shards.
        //  -   `isize::MAX` is not overflowed since the allocation succeeded for the number of shards.
        let pointer = unsafe { pointer.add(offset) };

        //  Safety:
        //  -   `pointer` points to `number_shards` initialized shards.
        unsafe { core::slice::from_raw_parts(pointer as *const u8 as *const Shard, number_shards) }
    }
}

impl<H, A> InternerHeader<H, A> {
    fn new(id: Id, hasher: H, director: ShardDirector<A>) -> Self {
        let ref_count = AtomicU64::new(0);

        Self {
            ref_count,
            id,
            hasher,
            director,
        }
    }
}

impl<H, A> fmt::Debug for InternerHeader<H, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Header")
            .field("id", &self.id)
            .field("director", &self.director)
            .finish()
    }
}

#[doc(hidden)]
pub mod compile_tests {

    //  Bad enough it needs to be `pub`, there's really no sense in exposing it any further.
    #![allow(dead_code)]

    /// ```compile_fail,E0277
    /// fn ensure_send<T: Send>() {}
    ///
    /// struct NoSendH(std::rc::Rc<u32>);
    ///
    /// ensure_send::<endor_interner::Interner<NoSendH>>();
    /// ```
    pub fn interner_not_send_if_hasher_not_send() {}

    /// ```compile_fail,E0277
    /// fn ensure_sync<T: Sync>() {}
    ///
    /// struct NoSyncH(std::cell::Cell<u32>);
    ///
    /// ensure_sync::<endor_interner::Interner<NoSyncH>>();
    /// ```
    pub fn interner_not_sync_if_hasher_not_sync() {}

    /// ```compile_fail,E0277
    /// #![feature(allocator_api)]
    ///
    /// fn ensure_send<T: Send>() {}
    ///
    /// struct NoSendA(std::rc::Rc<u32>);
    ///
    /// unsafe impl std::alloc::Allocator for NoSendA {
    ///     fn allocate(&self, _: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> { todo!() }
    ///     unsafe fn deallocate(&self, _: std::ptr::NonNull<u8>, _: std::alloc::Layout) { todo!() }
    /// }
    ///
    /// ensure_send::<endor_interner::Interner<endor_interner::DefaultFxBuildHasher, NoSendA>>();
    /// ```
    pub fn interner_not_send_if_allocator_not_send() {}

    /// ```compile_fail,E0277
    /// #![feature(allocator_api)]
    ///
    /// fn ensure_sync<T: Sync>() {}
    ///
    /// struct NoSyncA(std::cell::Cell<u32>);
    ///
    /// unsafe impl std::alloc::Allocator for NoSyncA {
    ///     fn allocate(&self, _: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> { todo!() }
    ///     unsafe fn deallocate(&self, _: std::ptr::NonNull<u8>, _: std::alloc::Layout) { todo!() }
    /// }
    ///
    /// ensure_sync::<endor_interner::Interner<endor_interner::DefaultFxBuildHasher, NoSyncA>>();
    /// ```
    pub fn interner_not_sync_if_allocator_not_sync() {}
} // mod compile_tests

#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_send<T: Send>() {}
    fn ensure_sync<T: Sync>() {}

    #[test]
    fn interner_send() {
        ensure_send::<Interner>();
    }

    #[test]
    fn interner_sync() {
        ensure_sync::<Interner>();
    }
} // mod tests
