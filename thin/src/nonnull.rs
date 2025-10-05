//! Thin pointers equivalent to `NonNull<T>`.
//!
//! For the layout of these thin pointers, refer to the crate-level documentation.

use core::{
    cmp, fmt, hash,
    marker::PhantomInvariant,
    panic,
    ptr::{NonNull, Pointee},
};

use crate::ThinPtrWith;

/// The thin equivalent of `NonNull<T>`.
pub type ThinNonNull<T> = ThinNonNullWith<T, ()>;

/// The thin equivalent of `NonNull<T>`, with a header of the user's choice.
#[repr(transparent)]
pub struct ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    ptr: NonNull<u8>,
    _data: PhantomInvariant<T>,
    _header: PhantomInvariant<H>,
}

//
//  Construction
//

impl<T, H> ThinNonNullWith<T, H> {
    /// Constructs a dangling pointer.
    ///
    /// The resulting pointer has no provenance.
    #[inline(always)]
    pub const fn dangling() -> Self {
        let layout = ThinPtrWith::<T, H>::layout();

        let dangling = layout.dangling();

        Self::from_raw(dangling)
    }
}

impl<T, H> ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    /// Constructs a new instance from a raw pointer.
    ///
    /// Unless this raw pointer refers to the thin pointer boundary in a memory block allocated according to
    /// `ThinLayout::new::<X, H, T, Y>()` for any `X` and `Y`, this function should probably not be used.
    #[inline(always)]
    pub const fn from_raw(ptr: NonNull<u8>) -> Self {
        let _data = PhantomInvariant::new();
        let _header = PhantomInvariant::new();

        Self { ptr, _data, _header }
    }

    /// Constructs a new instance from a thin pointer.
    ///
    /// Returns `None` if the thin pointer is null.
    #[inline(always)]
    pub const fn from_thin(ptr: ThinPtrWith<u8, H>) -> Option<Self> {
        NonNull::new(ptr.into_raw()).map(Self::from_raw)
    }

    /// Casts to another pointer type.
    #[inline(always)]
    pub const fn cast<U>(self) -> ThinNonNullWith<U, H>
    where
        U: ?Sized,
    {
        let Self { ptr, _header, .. } = self;

        let _data = PhantomInvariant::new();

        ThinNonNullWith { ptr, _data, _header }
    }
}

//
//  Destruction
//

impl<T, H> ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    /// Returns the underlying pointer.
    #[inline(always)]
    pub const fn into_raw(self) -> NonNull<u8> {
        self.ptr
    }

    /// Returns the thin pointer.
    #[inline(always)]
    pub const fn into_thin(self) -> ThinPtrWith<T, H> {
        ThinPtrWith::from_raw(self.ptr.as_ptr())
    }

    /// Executes the destructor, if any, of `T` and `H`.
    ///
    /// #   Safety
    ///
    /// -   Alive: the values of `T` and `H` must be valid for dropping.
    /// -   Data: either the data SHALL be zero-sized (`T: Sized`) or the pointer SHALL be a thin pointer, pointing into
    ///     a thin memory block.
    /// -   Header: either the header SHALL be zero-sized (`H: Sized`) or the pointer SHALL be a thin pointer, pointing
    ///     into a thin memory block.
    /// -   Metadata: either the metadata SHALL be zero-sized (`T: Sized`) or the pointer SHALL be a thin pointer,
    ///     pointing into a thin memory block.
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with an instance of `T`,
    ///     and a header `H`.
    #[inline(always)]
    pub unsafe fn drop_in_place(self) {
        //  Safety:
        //  -   Data, Metadata & Suitable: as per pre-conditions.
        let data = unsafe { self.as_ptr() };

        //  Safety:
        //  -   Valid: as per Data & Metadata pre-condition.
        //  -   Aligned, NonNull: as per Suitable pre-condition.
        //  -   ValidForDropping: as per Alive per-condition.
        unsafe { data.drop_in_place() };

        //  Safety:
        //  -   Header & Suitable: as per pre-conditions.
        let header = unsafe { self.as_header() };

        //  Safety:
        //  -   Valid: as per Header pre-condition.
        //  -   Aligned, NonNull: as per Suitable pre-condition.
        //  -   ValidForDropping: as per Alive per-condition.
        unsafe { header.drop_in_place() };
    }
}

//
//  High-level Access
//

impl<T, H> ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    /// Returns a pointer to `T`.
    ///
    /// #   Safety
    ///
    /// -   Metadata: either the metadata SHALL be zero-sized (`T: Sized`) or the pointer SHALL be a thin pointer,
    ///     pointing into a thin memory block.
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with an instance of `T`,
    ///     and a header `H`.
    #[inline(always)]
    pub const unsafe fn as_ptr(&self) -> NonNull<T> {
        let ptr = self.into_thin();

        //  Safety:
        //  -   Metadata & Suitable: as per pre-conditions.
        let ptr = unsafe { ptr.as_ptr() };

        //  Safety:
        //  -   NonNull: `self.ptr` was not null.
        unsafe { NonNull::new_unchecked(ptr) }
    }

    /// Returns a reference to `T`.
    ///
    /// #   Safety
    ///
    /// -   Metadata: either the metadata SHALL be zero-sized (`T: Sized`) or the pointer SHALL be a thin pointer,
    ///     pointing into a thin memory block.
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with an instance of `T`,
    ///     and a header `H`.
    /// -   Convertible: `self.as_ptr()` SHALL be convertible to a reference.
    #[inline(always)]
    pub const unsafe fn as_ref<'a>(&self) -> &'a T {
        let ptr = self.into_thin();

        //  Safety:
        //  -   Metadata & Suitable & Convertible: as per pre-conditions.
        unsafe { ptr.as_ref() }
    }

    /// Returns a mutable reference to `T`.
    ///
    /// #   Safety
    ///
    /// -   Metadata: either the metadata SHALL be zero-sized (`T: Sized`) or the pointer SHALL be a thin pointer,
    ///     pointing into a thin memory block.
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with an instance of `T`,
    /// -   Convertible: `self.as_ptr()` SHALL be convertible to a reference.
    ///     and a header `H`.
    #[inline(always)]
    pub const unsafe fn as_mut<'a>(&self) -> &'a mut T {
        let ptr = self.into_thin();

        //  Safety:
        //  -   Metadata & Suitable & Convertible: as per pre-conditions.
        unsafe { ptr.as_mut() }
    }

    /// Returns a reference to `H`.
    ///
    /// #   Safety
    ///
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with a header `H`.
    /// -   Convertible: `self.as_header()` SHALL be convertible to a reference.
    #[inline(always)]
    pub const unsafe fn as_header_ref<'a>(&self) -> &'a H {
        let ptr = self.into_thin();

        //  Safety:
        //  -   Suitable & Convertible: as per pre-conditions.
        unsafe { ptr.as_header_ref() }
    }

    /// Returns a mutable reference to `H`.
    ///
    /// #   Safety
    ///
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with a header `H`.
    /// -   Convertible: `self.as_ptr()` SHALL be convertible to a reference.
    ///     and a header `H`.
    #[inline(always)]
    pub const unsafe fn as_header_mut<'a>(&self) -> &'a mut H {
        let ptr = self.into_thin();

        //  Safety:
        //  -   Suitable & Convertible: as per pre-conditions.
        unsafe { ptr.as_header_mut() }
    }
}

//
//  Low-level Access
//

impl<T, H> ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    /// Returns a pointer to the data portion of `T`.
    #[inline(always)]
    pub const fn as_data(&self) -> NonNull<u8> {
        let ptr = self.into_thin();

        let data = ptr.as_data();

        //  Safety:
        //  -   NonNull: `self.ptr` was not null.
        unsafe { NonNull::new_unchecked(data) }
    }

    /// Returns a pointer to the header `H`.
    ///
    /// #   Safety
    ///
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with a header `H`.
    #[inline(always)]
    pub const unsafe fn as_header(&self) -> NonNull<H> {
        let ptr = self.into_thin();

        //  Safety:
        //  -   Suitable: a per pre-condition.
        let header = unsafe { ptr.as_header() };

        //  Safety:
        //  -   NonNull: `self.ptr` was not null.
        unsafe { NonNull::new_unchecked(header) }
    }

    /// Returns a pointer to the metadata.
    ///
    /// #   Safety
    ///
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with a header `H`.
    #[inline(always)]
    pub const unsafe fn as_metadata(&self) -> NonNull<<T as Pointee>::Metadata> {
        let ptr = self.into_thin();

        //  Safety:
        //  -   Suitable: a per pre-condition.
        let metadata = unsafe { ptr.as_metadata() as *mut _ };

        //  Safety:
        //  -   NonNull: `self.ptr` was not null.
        unsafe { NonNull::new_unchecked(metadata) }
    }
}

//
//  Traits
//

impl<T, H> Clone for ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, H> Copy for ThinNonNullWith<T, H> where T: ?Sized {}

impl<T, H> fmt::Debug for ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Pointer::fmt(&self.ptr, f)
    }
}

impl<T, H> fmt::Pointer for ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Pointer::fmt(&self.ptr, f)
    }
}

impl<T, H> Eq for ThinNonNullWith<T, H> where T: ?Sized {}

impl<T, H> PartialEq for ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T, H> hash::Hash for ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn hash<HR>(&self, state: &mut HR)
    where
        HR: hash::Hasher,
    {
        self.ptr.hash(state);
    }
}

impl<T, H> Ord for ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.ptr.cmp(&other.ptr)
    }
}

impl<T, H> PartialOrd for ThinNonNullWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T, H> panic::UnwindSafe for ThinNonNullWith<T, H>
where
    T: panic::RefUnwindSafe + ?Sized,
    H: panic::RefUnwindSafe,
{
}
