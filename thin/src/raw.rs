//! Handles the actual memory finnicky details of allocation.

use core::{
    alloc::Layout,
    hint, intrinsics,
    marker::{PhantomInvariant, Unsize},
    mem::{self, MaybeUninit},
    ptr::{self, NonNull},
};

use alloc::alloc::{AllocError, Allocator};

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
        let is_value_zst = mem::size_of::<T>() == 0 && mem::size_of::<H>() == 0 && mem::size_of::<A>() == 0;

        let metadata = ptr::metadata(&value as &U);

        if is_value_zst && mem::size_of_val(&metadata) == 0 {
            mem::forget(value);
            mem::forget(header);
            mem::forget(allocator);

            let layout = ThinLayout::new::<T, H, U, A>();

            return Ok(layout.dangling());
        }

        if is_value_zst {
            mem::forget(header);
            mem::forget(allocator);

            //  Must be done in a const block, to ensure the allocation is really a constant-time allocation.
            let ptr = const {
                let layout = ThinLayout::new::<T, H, U, A>();

                let block = layout.block();

                //  Safety:
                //  -   CompileTime: within a `const` block.
                let start = unsafe { intrinsics::const_allocate(block.size(), block.align()) };

                //  Safety:
                //  -   InBounds: allocated as per layout.
                let ptr = unsafe { start.add(layout.start_offset()) };

                let metadata = ptr::metadata::<U>(ptr::dangling::<T>() as *const U);

                //  Safety:
                //  -   Valid: freshly allocated.
                //  -   Aligned: allocated as per layout.
                unsafe { ptr::write(ptr.sub(layout.metadata_offset()) as *mut _, metadata) };

                //  Safety:
                //  -   No prerequisite. Mimicks unstable alloc::boxed::ThinBox.
                unsafe { intrinsics::const_make_global(start) };

                ptr
            };

            //  Safety:
            //  -   NonNull: `const_allocate` does not return null pointers at compile-time.
            return Ok(unsafe { NonNull::new_unchecked(ptr) });
        }

        let layout = ThinLayout::new::<T, H, U, A>();

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
}

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
    /// -   EndOfLife: both this instance and any of its copies SHALL never be used again after a call to this function.
    pub(crate) unsafe fn drop(&mut self) {
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

        //  Safety:
        //  -   Metadata & Suitable: suitably allocated.
        let value = unsafe { self.ptr.as_ptr() };

        //  Safety:
        //  -   Suitable: suitably allocated.
        let header = unsafe { self.ptr.as_header() };

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

        let _guard = DropGuard {
            //  Do not drop a ZST, it is either dangling or const-allocated.
            ptr: (!is_zst).then_some(self.as_block()),
            layout: layout.block(),
            allocator,
        };

        //  Safety:
        //  -   Valid: `header` and `value` are valid to drop as per EndOfLife pre-condition.
        unsafe {
            header.drop_in_place();
            value.drop_in_place();
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
