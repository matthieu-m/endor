//! Handles the actual memory finnicky details of allocation.

use core::{
    alloc::Layout,
    hint,
    marker::{PhantomInvariant, Unsize},
    mem::{self, MaybeUninit},
    ptr::{self, NonNull},
};

use alloc::{
    alloc::{AllocError, Allocator},
    boxed::ThinBox,
};

use crate::{ThinLayout, ThinNonNullWith};

/// Handles allocation, moving values in, moving values out, and deallocation.
#[repr(transparent)]
pub(crate) struct ThinRawWith<T, H, A>
where
    T: ?Sized,
{
    //  Safety:
    //  -   Suitable: `ptr` always points to a suitable memory block for `T`, `H`, and `A`.
    //      It may be dangling, or const-allocated, but it is always suitable.
    ptr: ThinNonNullWith<T, H>,
    _allocator: PhantomInvariant<A>,
}

//
//  Conversion
//

impl<T, H, A> ThinRawWith<T, H, A>
where
    T: ?Sized,
{
    /// Constructs an instance from a raw pointer.
    ///
    /// #   Safety
    ///
    /// -   RoundTrip: `ptr` must have been obtained by a call to `Self::into_non_null`.
    #[inline(always)]
    pub(crate) unsafe fn from_non_null(ptr: ThinNonNullWith<T, H>) -> Self {
        let _allocator = PhantomInvariant::new();

        Self { ptr, _allocator }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub(crate) fn into_non_null(self) -> ThinNonNullWith<T, H> {
        self.ptr
    }
}

impl<T, H, A> ThinRawWith<T, H, A>
where
    A: Allocator,
{
    /// Returns the elements, and the allocator.
    ///
    /// #   Safety
    ///
    /// -   EndOfLife: both this instance and any of its copies SHALL never be dereferenced again until the value &
    ///     header have been replaced.
    #[inline]
    pub(crate) unsafe fn into_inner(this: Self) -> (T, H, A) {
        //  Safety:
        //  -   EndOfLife: as pre-condition.
        let (value, header, uninit) = unsafe { Self::take(this) };

        //  Ensure we really have the right type.
        let uninit: ThinRawWith<MaybeUninit<T>, MaybeUninit<H>, A> = uninit;

        //  Safety:
        //  -   EndOfLife: as pre-condition.
        let allocator = unsafe { ThinRawWith::into_allocator(uninit) };

        (value, header, allocator)
    }

    /// Returns the elements, and an allocation suitable to place them.
    ///
    /// #   Safety
    ///
    /// -   EndOfLife: both this instance and any of its copies SHALL never be dereferenced again until the value &
    ///     header have been replaced.
    #[inline]
    pub(crate) unsafe fn take(this: Self) -> (T, H, ThinRawWith<MaybeUninit<T>, MaybeUninit<H>, A>) {
        //  Minimum level of type inference: the result is directly returned.
        #![allow(clippy::missing_transmute_annotations)]

        //  Safety:
        //  -   Metadata: none.
        //  -   Suitable: per invariant.
        let value = unsafe { this.ptr.as_ptr() };

        //  Safety:
        //  -   Suitable: per invariant.
        //  -   Valid: per EndOfLife pre-condition.
        let value = unsafe { value.read() };

        //  Safety:
        //  -   Suitable: per invariant.
        let header = unsafe { this.ptr.as_header() };

        //  Safety:
        //  -   Suitable: per invariant.
        //  -   Valid: per EndOfLife pre-condition.
        let header = unsafe { header.read() };

        //  Safety:
        //  -   Transmutable:
        //      -   `#[repr(transparent)]` down to `NonNull<u8>`.
        //      -   `MaybeUninit<T>` is itself `#[repr(transparent)]` with `T`.
        let result = unsafe { mem::transmute::<Self, _>(this) };

        (value, header, result)
    }
}

impl<T, H, A> ThinRawWith<MaybeUninit<T>, MaybeUninit<H>, A>
where
    A: Allocator,
{
    /// Converts to `ThinRawWith<T, H, A>`.
    ///
    /// #   Safety
    ///
    /// -   Initialized: as per `MaybeUninit::assume_init`.
    #[inline(always)]
    pub(crate) unsafe fn assume_init(this: Self) -> ThinRawWith<T, H, A> {
        //  Safety:
        //  -   Transmutable:
        //      -   `#[repr(transparent)]` down to `NonNull<u8>`.
        //      -   `MaybeUninit<T>` is itself `#[repr(transparent)]` with `T`.
        unsafe { mem::transmute::<Self, _>(this) }
    }

    /// Initializes the uninitialized parts of `self`.
    ///
    /// #   Safety:
    ///
    /// -   Mutable: no other copy of `this` SHALL be used to access value and header during this call.
    #[inline]
    pub(crate) unsafe fn write(this: Self, value: T, header: H) -> ThinRawWith<T, H, A> {
        //  Safety:
        //  -   Suitable: as per invariant.
        //  -   Mutable: as per pre-condition.
        let value_slot = unsafe { this.ptr.as_mut() };

        value_slot.write(value);

        //  Safety:
        //  -   Suitable: as per invariant.
        //  -   Mutable: as per pre-condition.
        let header_slot = unsafe { this.ptr.as_header_mut() };

        header_slot.write(header);

        //  Safety:
        //  -   Initialized: just written.
        unsafe { Self::assume_init(this) }
    }

    /// Recovers the allocator.
    ///
    /// It is up to the caller to ensure that `T` and `H` are indeed uninitialized, their destructors WILL NOT be
    /// called.
    ///
    /// #   Safety
    ///
    /// -   EndOfLife: both this instance and any of its copies SHALL never be dereferenced again until the value &
    ///     header have been replaced.
    #[inline]
    pub(crate) unsafe fn into_allocator(this: Self) -> A {
        let layout = this.layout();

        let ptr = this.as_block();
        let allocator = this.as_allocator();

        //  Safety:
        //  -   Suitable: per invariant, if possibly unaligned.
        //  -   Valid: per EndOfLife pre-condition.
        let allocator = unsafe { allocator.read_unaligned() };

        //  Safety:
        //  -   SameAllocator: `ptr` was allocated by `allocator`.
        //  -   FitLayout: `ptr` was allocated with `layout.block()`.
        unsafe { allocator.deallocate(ptr, layout.block()) };

        allocator
    }
}

impl<T, H, A> ThinRawWith<[MaybeUninit<T>], MaybeUninit<H>, A>
where
    A: Allocator,
{
    /// Converts to `ThinRawWith<[T], H, A>`.
    ///
    /// #   Safety
    ///
    /// -   Initialized: as per `MaybeUninit::assume_init`.
    #[inline(always)]
    pub(crate) unsafe fn assume_init(this: Self) -> ThinRawWith<[T], H, A> {
        //  Safety:
        //  -   Transmutable:
        //      -   `#[repr(transparent)]` down to `NonNull<u8>`.
        //      -   `MaybeUninit<T>` is itself `#[repr(transparent)]` with `T`.
        unsafe { mem::transmute::<Self, _>(this) }
    }
}

//
//  Construction
//

impl<T, H, A> ThinRawWith<T, H, A>
where
    A: Allocator,
{
    /// Attempts to allocate, if necessary, moves the `value`, `header`, and `allocator` in, and returns an instance.
    #[inline(always)]
    pub(crate) fn try_new(value: T, header: H, allocator: A) -> Result<Self, AllocError> {
        let raw = Self::try_raw(value, header, allocator)?;

        let ptr = ThinNonNullWith::from_raw(raw);
        let _allocator = PhantomInvariant::new();

        Ok(Self { ptr, _allocator })
    }
}

impl<T, H, A> ThinRawWith<T, H, A>
where
    A: Allocator,
{
    //  Safety:
    //  -   Suitable: the allocated memory is suitable.
    fn try_raw(value: T, header: H, allocator: A) -> Result<NonNull<u8>, AllocError> {
        let is_zst = const { mem::size_of::<T>() == 0 && mem::size_of::<H>() == 0 && mem::size_of::<A>() == 0 };

        let layout = ThinLayout::new::<T, H, T, A>();

        if is_zst {
            mem::forget(value);
            mem::forget(header);
            mem::forget(allocator);

            return Ok(layout.dangling());
        }

        let ptr = allocator.allocate(layout.block()).map(NonNull::as_non_null_ptr)?;

        //  Safety:
        //  -   InBounds: allocated as per `layout`.
        let ptr = unsafe { ptr.add(layout.start_offset()) };

        //  Safety:
        //  -   InBounds: allocated as per `Layout`.
        //  -   Aligned: `value` and `header` are written to suitably aligned locations.
        unsafe {
            ptr.cast::<T>().write(value);
            ptr.sub(layout.header_offset()).cast::<H>().write(header);
            ptr.sub(layout.allocator_offset())
                .cast::<A>()
                .write_unaligned(allocator);
        }

        Ok(ptr)
    }
}

impl<U, H, A> ThinRawWith<U, H, A>
where
    U: ?Sized,
    A: Allocator,
{
    /// Attempts to allocate, if necessary, moves the `value`, `header`, and `allocator` in, and returns an instance.
    #[inline(always)]
    pub(crate) fn try_new_unsize<T>(value: T, header: H, allocator: A) -> Result<Self, AllocError>
    where
        T: Unsize<U>,
    {
        let raw = Self::try_raw_unsize(value, header, allocator)?;

        let ptr = ThinNonNullWith::from_raw(raw);
        let _allocator = PhantomInvariant::new();

        Ok(Self { ptr, _allocator })
    }
}

impl<U, H, A> ThinRawWith<U, H, A>
where
    U: ?Sized,
    A: Allocator,
{
    //  Safety:
    //  -   Suitable: the allocated memory is suitable.
    fn try_raw_unsize<T>(value: T, header: H, allocator: A) -> Result<NonNull<u8>, AllocError>
    where
        T: Unsize<U>,
    {
        let is_value_zst = const { mem::size_of::<T>() == 0 && mem::size_of::<H>() == 0 && mem::size_of::<A>() == 0 };

        if is_value_zst {
            mem::forget(header);
            mem::forget(allocator);

            return Self::try_raw_unsize_szt(value);
        }

        let layout = ThinLayout::new::<T, H, U, A>();
        let metadata = ptr::metadata(&value as &U);

        let ptr = allocator.allocate(layout.block()).map(NonNull::as_non_null_ptr)?;

        //  Safety:
        //  -   InBounds: allocated as per `layout`.
        let ptr = unsafe { ptr.add(layout.start_offset()) };

        //  Safety:
        //  -   InBounds: allocated as per `Layout`.
        //  -   Aligned: `value`, `header`, and `metadata` are written to suitably aligned locations.
        unsafe {
            ptr.cast::<T>().write(value);
            ptr.sub(layout.header_offset()).cast::<H>().write(header);
            ptr.sub(layout.metadata_offset()).cast().write(metadata);
            ptr.sub(layout.allocator_offset())
                .cast::<A>()
                .write_unaligned(allocator);
        }

        Ok(ptr)
    }

    //  Safety:
    //  -   Suitable: the allocated memory is suitable.
    fn try_raw_unsize_szt<T>(value: T) -> Result<NonNull<u8>, AllocError>
    where
        T: Unsize<U>,
    {
        //  ThinBox implements a clever trick to avoid allocating _just_ for metadata, by instead creating a static
        //  variable with said metadata, in a block of memory suitably aligned for it.
        //
        //  Using this trick is desirable, obviously, but hard to achieve. It relies on compiler intrinsics, which are
        //  never intended for stabilization, and worse, poorly documented and finnicky to use, easily leading to
        //  internal compiler errors.
        //
        //  Instead, the trick is therefore to leverage ThinBox to perform this trick for us. The difficulty is in
        //  obtaining out of it a block of memory that is suitably aligned not only for `T`, but also for `H`.
        //
        //  Using `[H; 0]` will force ThinBox to over-align the pointer it uses, if `T` was not aligned enough. This is
        //  a good _start_, as it guarantees that `ptr.sub(layout.header_offset)` will be sufficiently aligned. It does
        //  not, however, guarantee that this pointer will be non-null.
        //
        //  The pointer could be null: ThinBox only offsets the pointer "just" enough to place the metadata in:
        //
        //  -   If the alignment of `([H; 0], T)` is less than or equal to the size & alignment of the metadata.
        //  -   If the alignment of `H` is greater than or equal to that of `T`.
        //
        //  There is no way to force ThinBox to have a greater offset from zero, other than alignment, and therefore
        //  we will tweak the layout by using an overaligned struct.
        use core::ptr::Pointee;

        use aligned::*;

        fn allocate_zst<T, DH, U>(value: T) -> NonNull<u8>
        where
            T: Unsize<U>,
            U: ?Sized,
        {
            struct Block<DH, T: ?Sized> {
                _header: [DH; 0],
                _t: T,
            }

            let block: Block<DH, T> = Block { _header: [], _t: value };

            assert_eq!(0, mem::size_of_val(&block));

            let mut thin: ThinBox<Block<DH, U>> = ThinBox::new_unsize(block);

            //  Miri complains that this only gives access to [0x10..0x10] in the memory block, and not [0x8..0x10],
            //  that is, that this does not allow accessing the metadata stored prior to T, when using the Stacked
            //  Borrows model. It accepts the code with the Tree Borrows model.
            let ptr = NonNull::from_mut(&mut *thin);

            mem::forget(thin);

            ptr.cast()
        }

        let min_align = const {
            let h = mem::align_of::<H>();

            //  Commonly (2, 2) on 16-bits platforms, (4, 4) on 32-bits platforms, and (8, 8) on 64-bits platforms...
            //  ... but there's no reason not to make it just work.
            let m = Layout::new::<<U as Pointee>::Metadata>();

            let m = if m.size() > m.align() {
                //  If it overflows an returns 0, the next match will lead to Err(AllocError): perfect!
                m.size().next_power_of_two()
            } else {
                m.align()
            };

            if h > m { h } else { m }
        };

        match min_align {
            1 => Ok(allocate_zst::<T, Align_2, U>(value)),
            2 => Ok(allocate_zst::<T, Align_4, U>(value)),
            4 => Ok(allocate_zst::<T, Align_8, U>(value)),
            8 => Ok(allocate_zst::<T, Align_16, U>(value)),
            16 => Ok(allocate_zst::<T, Align_32, U>(value)),
            32 => Ok(allocate_zst::<T, Align_64, U>(value)),
            64 => Ok(allocate_zst::<T, Align_128, U>(value)),
            128 => Ok(allocate_zst::<T, Align_256, U>(value)),
            256 => Ok(allocate_zst::<T, Align_512, U>(value)),
            512 => Ok(allocate_zst::<T, Align_1_024, U>(value)),
            1_024 => Ok(allocate_zst::<T, Align_2_048, U>(value)),
            2_048 => Ok(allocate_zst::<T, Align_4_096, U>(value)),
            4_096 => Ok(allocate_zst::<T, Align_8_192, U>(value)),
            8_192 => Ok(allocate_zst::<T, Align_16_384, U>(value)),
            16_384 => Ok(allocate_zst::<T, Align_32_768, U>(value)),
            32_768 => Ok(allocate_zst::<T, Align_65_536, U>(value)),
            65_536 => Ok(allocate_zst::<T, Align_131_072, U>(value)),
            131_072 => Ok(allocate_zst::<T, Align_262_144, U>(value)),
            262_144 => Ok(allocate_zst::<T, Align_524_288, U>(value)),
            524_288 => Ok(allocate_zst::<T, Align_1_048_576, U>(value)),
            1_048_576 => Ok(allocate_zst::<T, Align_2_097_152, U>(value)),
            2_097_152 => Ok(allocate_zst::<T, Align_4_194_304, U>(value)),
            4_194_304 => Ok(allocate_zst::<T, Align_8_388_608, U>(value)),
            8_388_608 => Ok(allocate_zst::<T, Align_16_777_216, U>(value)),
            16_777_216 => Ok(allocate_zst::<T, Align_33_554_432, U>(value)),
            33_554_432 => Ok(allocate_zst::<T, Align_67_108_864, U>(value)),
            67_108_864 => Ok(allocate_zst::<T, Align_134_217_728, U>(value)),
            134_217_728 => Ok(allocate_zst::<T, Align_268_435_456, U>(value)),
            268_435_456 => Ok(allocate_zst::<T, Align_536_870_912, U>(value)),
            _ => Err(AllocError),
        }
    }
}

mod aligned {
    //  The underscore is very much necessary to see _anything_.
    #![allow(non_camel_case_types)]

    #[repr(align(2))]
    pub(super) struct Align_2;

    #[repr(align(4))]
    pub(super) struct Align_4;

    #[repr(align(8))]
    pub(super) struct Align_8;

    #[repr(align(16))]
    pub(super) struct Align_16;

    #[repr(align(32))]
    pub(super) struct Align_32;

    #[repr(align(64))]
    pub(super) struct Align_64;

    #[repr(align(128))]
    pub(super) struct Align_128;

    #[repr(align(256))]
    pub(super) struct Align_256;

    #[repr(align(512))]
    pub(super) struct Align_512;

    #[repr(align(1_024))]
    pub(super) struct Align_1_024;

    #[repr(align(2_048))]
    pub(super) struct Align_2_048;

    #[repr(align(4_096))]
    pub(super) struct Align_4_096;

    #[repr(align(8_192))]
    pub(super) struct Align_8_192;

    #[repr(align(16_384))]
    pub(super) struct Align_16_384;

    #[repr(align(32_768))]
    pub(super) struct Align_32_768;

    #[repr(align(65_536))]
    pub(super) struct Align_65_536;

    #[repr(align(131_072))]
    pub(super) struct Align_131_072;

    #[repr(align(262_144))]
    pub(super) struct Align_262_144;

    #[repr(align(524_288))]
    pub(super) struct Align_524_288;

    #[repr(align(1_048_576))]
    pub(super) struct Align_1_048_576;

    #[repr(align(2_097_152))]
    pub(super) struct Align_2_097_152;

    #[repr(align(4_194_304))]
    pub(super) struct Align_4_194_304;

    #[repr(align(8_388_608))]
    pub(super) struct Align_8_388_608;

    #[repr(align(16_777_216))]
    pub(super) struct Align_16_777_216;

    #[repr(align(33_554_432))]
    pub(super) struct Align_33_554_432;

    #[repr(align(67_108_864))]
    pub(super) struct Align_67_108_864;

    #[repr(align(134_217_728))]
    pub(super) struct Align_134_217_728;

    #[repr(align(268_435_456))]
    pub(super) struct Align_268_435_456;

    #[repr(align(536_870_912))]
    pub(super) struct Align_536_870_912;

    //  Only alignments up to 2^29 (536MB) are supported.

    #[test]
    fn alignment() {
        use core::mem;

        assert!(mem::align_of::<Align_2>() >= 2);
        assert!(mem::align_of::<Align_4>() >= 4);
        assert!(mem::align_of::<Align_8>() >= 8);
        assert!(mem::align_of::<Align_16>() >= 16);
        assert!(mem::align_of::<Align_32>() >= 32);
        assert!(mem::align_of::<Align_64>() >= 64);
        assert!(mem::align_of::<Align_128>() >= 128);
        assert!(mem::align_of::<Align_256>() >= 256);
        assert!(mem::align_of::<Align_512>() >= 512);
        assert!(mem::align_of::<Align_1_024>() >= 1_024);
        assert!(mem::align_of::<Align_2_048>() >= 2_048);
        assert!(mem::align_of::<Align_4_096>() >= 4_096);
        assert!(mem::align_of::<Align_8_192>() >= 8_192);
        assert!(mem::align_of::<Align_16_384>() >= 16_384);
        assert!(mem::align_of::<Align_32_768>() >= 32_368);
        assert!(mem::align_of::<Align_65_536>() >= 65_536);
        assert!(mem::align_of::<Align_131_072>() >= 131_072);
        assert!(mem::align_of::<Align_262_144>() >= 262_144);
        assert!(mem::align_of::<Align_524_288>() >= 524_288);
        assert!(mem::align_of::<Align_1_048_576>() >= 1_048_576);
        assert!(mem::align_of::<Align_2_097_152>() >= 2_097_152);
        assert!(mem::align_of::<Align_4_194_304>() >= 4_194_304);
        assert!(mem::align_of::<Align_8_388_608>() >= 8_388_608);
        assert!(mem::align_of::<Align_16_777_216>() >= 16_777_216);
        assert!(mem::align_of::<Align_33_554_432>() >= 33_554_432);
        assert!(mem::align_of::<Align_67_108_864>() >= 67_108_864);
        assert!(mem::align_of::<Align_134_217_728>() >= 134_217_728);
        assert!(mem::align_of::<Align_268_435_456>() >= 268_435_456);
        assert!(mem::align_of::<Align_536_870_912>() >= 536_870_912);
    }
} // mod aligned

//
//  Destruction
//

impl<T, H, A> ThinRawWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Drops the content of the memory block, and deallocates it.
    ///
    /// The `Drop` trait is explicitly not implemented, as reference-counted uses of this type require a bit more
    /// flexibility.
    ///
    /// #   Safety
    ///
    /// -   Droppable: the header and value should be droppable.
    /// -   EndOfLife: both this instance and any of its copies SHALL never be used again after a call to this function.
    pub(crate) unsafe fn drop(&mut self) {
        //  Safety:
        //  -   EndOfLife: as per pre-condition.
        let _guard = unsafe { self.drop_guard() };

        //  Safety:
        //  -   Droppable: as per Droppable pre-condition.
        unsafe { self.drop_in_place() }
    }

    /// Drop the value & header in place.
    ///
    /// The allocation remains valid, and may be reused.
    ///
    /// #   Safety:
    ///
    /// -   Droppable: the header and value should be droppable.
    pub(crate) unsafe fn drop_in_place(&mut self) {
        //  Safety:
        //  -   Metadata & Suitable: suitably allocated.
        let value = unsafe { self.ptr.as_ptr() };

        //  Safety:
        //  -   Suitable: suitably allocated.
        let header = unsafe { self.ptr.as_header() };

        //  Safety:
        //  -   Valid: `header` and `value` are valid to drop as per EndOfLife pre-condition.
        unsafe {
            header.drop_in_place();
            value.drop_in_place();
        }
    }

    /// Deallocates the memory.
    ///
    /// #   Safety
    ///
    /// -   EndOfLife: the memory allocation is dropped when the guard is, with all the consequences one should expect.
    pub(crate) unsafe fn drop_guard(&mut self) -> impl Drop + use<T, H, A> {
        //  Ensure deallocation even if the value or header panic during the drop.
        struct DropGuard<A>
        where
            A: Allocator,
        {
            ptr: Option<NonNull<u8>>,
            layout: Layout,
            allocator: A,
        }

        impl<A> Drop for DropGuard<A>
        where
            A: Allocator,
        {
            fn drop(&mut self) {
                let Some(ptr) = self.ptr else { return };

                //  Safety:
                //  -   SameAllocator: `ptr` was allocated by `self.allocator`.
                //  -   FitLayout: `ptr` was allocated with `self.layout`.
                unsafe { self.allocator.deallocate(ptr, self.layout) };
            }
        }

        let layout = self.layout();

        let is_zst =
            layout.block().size() == layout.start_offset() && mem::size_of::<H>() == 0 && mem::size_of::<A>() == 0;

        let allocator: A = {
            let allocator = self.as_allocator();

            //  Safety:
            //  -   Read: either ZST in which case all reads are valid, or otherwise a memory block was allocated and
            //      `allocator` was moved at this offset.
            //  -   Live: as per the EndOfLife pre-condition, `allocator` was never read out of this location before.
            unsafe { allocator.read_unaligned() }
        };

        DropGuard {
            //  Do not drop a ZST, it is either dangling or const-allocated.
            ptr: (!is_zst).then_some(self.as_block()),
            layout: layout.block(),
            allocator,
        }
    }
}

//
//  High-level Access
//

impl<T, H, A> ThinRawWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub(crate) const fn as_non_null(&self) -> ThinNonNullWith<T, H> {
        self.ptr
    }

    /// Returns a reference to the data.
    ///
    /// #   Safety:
    ///
    /// -   Convertible: `self.as_ptr().as_ptr()` SHALL be convertible to a reference.
    #[inline(always)]
    pub(crate) const unsafe fn as_ref<'a>(&self) -> &'a T {
        //  Safety:
        //  -   Metadata & Suitable: as per invariant.
        //  -   Convertible: as per pre-condition.
        unsafe { self.ptr.as_ref() }
    }

    /// Returns a reference to the data.
    ///
    /// #   Safety:
    ///
    /// -   Convertible: `self.as_ptr().as_ptr()` SHALL be convertible to a reference.
    #[inline(always)]
    pub(crate) const unsafe fn as_mut<'a>(&self) -> &'a mut T {
        //  Safety:
        //  -   Metadata & Suitable: as per invariant.
        //  -   Convertible: as per pre-condition.
        unsafe { self.ptr.as_mut() }
    }

    /// Returns a reference to `H`.
    ///
    /// #   Safety
    ///
    /// -   Convertible: `self.as_ptr().as_header()` SHALL be convertible to a reference.
    #[inline(always)]
    pub(crate) const unsafe fn as_header_ref<'a>(&self) -> &'a H {
        //  Safety:
        //  -   Suitable: as per invariant.
        //  -   Convertible: as per pre-condition.
        unsafe { self.ptr.as_header_ref() }
    }

    /// Returns a mutable reference to `H`.
    ///
    /// #   Safety
    ///
    /// -   Convertible: `self.as_ptr().as_header()` SHALL be convertible to a reference.
    #[inline(always)]
    pub(crate) const unsafe fn as_header_mut<'a>(&self) -> &'a mut H {
        //  Safety:
        //  -   Suitable: as per invariant.
        //  -   Convertible: as per pre-condition.
        unsafe { self.ptr.as_header_mut() }
    }
}

//
//  Low-level Access
//

impl<T, H, A> ThinRawWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns a pointer to the start of the memory block.
    #[inline(always)]
    pub const fn as_block(&self) -> NonNull<u8> {
        let layout = self.layout();

        //  Safety:
        //  -   Suitable: per invariant.
        //  -   SameLayout: initially allocated with `layout`.
        self.ptr.as_block(layout)
    }

    /// Returns a pointer to the allocator.
    ///
    /// The pointer MAY NOT be suitably aligned for `A`.
    #[inline(always)]
    pub const fn as_allocator(&self) -> NonNull<A> {
        let layout = self.layout();

        //  Safety:
        //  -   Suitable: per invariant.
        //  -   SameLayout: initially allocated with `layout`.
        unsafe { self.ptr.as_allocator(layout) }
    }

    /// Returns the thin layout.
    #[inline(always)]
    pub const fn layout(&self) -> ThinLayout {
        //  Safety:
        //  -   Metadata & Suitable: per invariant.
        let value = unsafe { self.ptr.as_ptr() };

        //  Safety:
        //  -   Convertible: `value` is either a valid value, or is a zero-sized type.
        let Ok(layout) = ThinLayout::for_value::<_, H, A>(unsafe { value.as_ref() }) else {
            //  Safety:
            //  -   This block was allocated, therefore computation succeeded already.
            unsafe { hint::unreachable_unchecked() }
        };

        layout
    }
}

//
//  Clone/Copy
//

impl<T, H, A> Clone for ThinRawWith<T, H, A>
where
    T: ?Sized,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, H, A> Copy for ThinRawWith<T, H, A> where T: ?Sized {}
