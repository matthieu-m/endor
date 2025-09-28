//! Thin pointers equivalent to `*mut T`.
//!
//! For the layout of these thin pointers, refer to the crate-level documentation.

use core::{
    cmp, fmt, hash,
    marker::PhantomInvariant,
    ptr::{self, Pointee},
};

use crate::ThinLayout;

/// The thin equivalent of `*mut T`.
pub type ThinPtr<T> = ThinPtrWith<T, ()>;

/// The thin equivalent of `*mut T`, with a header of the user's choice.
///
/// If you wish to drop the data, first convert to a `ThinNonNullWith`, then use its `drop_in_place` method.
pub struct ThinPtrWith<T, H>
where
    T: ?Sized,
{
    ptr: *mut u8,
    _data: PhantomInvariant<T>,
    _header: PhantomInvariant<H>,
}

//
//  Construction
//

impl<T> ThinPtrWith<T, ()> {
    /// Constructs a null pointer.
    #[inline(always)]
    pub const fn null() -> Self {
        Self::from_raw(ptr::null_mut())
    }
}

impl<T, H> ThinPtrWith<T, H> {
    /// Constructs a dangling pointer.
    ///
    /// The resulting pointer has no provenance.
    #[inline(always)]
    pub const fn dangling() -> Self {
        let layout = Self::layout();

        let dangling = layout.dangling();

        Self::from_raw(dangling.as_ptr())
    }
}

impl<T, H> ThinPtrWith<T, H>
where
    T: ?Sized,
{
    /// Constructs a new instance from a raw pointer.
    ///
    /// Unless this raw pointer refers to the thin pointer boundary in a memory block allocated according to
    /// `ThinLayout::new::<X, H, T, Y>()` for any `X` and `Y`, this function should probably not be used.
    #[inline(always)]
    pub const fn from_raw(ptr: *mut u8) -> Self {
        let _data = PhantomInvariant::new();
        let _header = PhantomInvariant::new();

        Self { ptr, _data, _header }
    }

    /// Casts to another pointer type.
    #[inline(always)]
    pub const fn cast<U>(self) -> ThinPtrWith<U, H>
    where
        U: ?Sized,
    {
        let Self { ptr, _header, .. } = self;

        let _data = PhantomInvariant::new();

        ThinPtrWith { ptr, _data, _header }
    }
}

impl<T> Default for ThinPtrWith<T, ()> {
    fn default() -> Self {
        Self::null()
    }
}

//
//  Destruction
//

impl<T, H> ThinPtrWith<T, H>
where
    T: ?Sized,
{
    /// Returns the underlying pointer.
    #[inline(always)]
    pub const fn into_raw(self) -> *mut u8 {
        self.ptr
    }
}

//
//  High-level Access
//

impl<T, H> ThinPtrWith<T, H>
where
    T: ?Sized,
{
    /// Returns whether the pointer is null, or not.
    #[inline(always)]
    pub const fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    /// Returns a pointer to `T`.
    ///
    /// #   Safety
    ///
    /// -   Metadata: either the metadata SHALL be zero-sized (`T: Sized`) or the pointer SHALL be a thin pointer,
    ///     pointing into a thin memory block.
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with an instance of `T`,
    ///     and a header `H`.
    #[inline(always)]
    pub const unsafe fn as_ptr(&self) -> *mut T {
        let data = self.as_data();

        //  Safety:
        //  -   ZST or Derefenceable: as per pre-condition.
        let metadata = unsafe { *self.as_metadata() };

        ptr::from_raw_parts_mut(data, metadata)
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
        //  Safety:
        //  -   Metadata, Suitable: as per pre-conditions.
        let ptr = unsafe { self.as_ptr() };

        //  Safety:
        //  -   Convertible: as per pre-condition.
        unsafe { &*ptr }
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
        //  Safety:
        //  -   Metadata, Suitable: as per pre-conditions.
        let ptr = unsafe { self.as_ptr() };

        //  Safety:
        //  -   Convertible: as per pre-condition.
        unsafe { &mut *ptr }
    }

    /// Returns a reference to `H`.
    ///
    /// #   Safety
    ///
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with a header `H`.
    /// -   Convertible: `self.as_header()` SHALL be convertible to a reference.
    #[inline(always)]
    pub const unsafe fn as_header_ref<'a>(&self) -> &'a H {
        //  Safety:
        //  -   Suitable: a per pre-condition.
        let ptr = unsafe { self.as_header() };

        //  Safety:
        //  -   Convertible: as per pre-condition.
        unsafe { &*ptr }
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
        //  Safety:
        //  -   Suitable: a per pre-condition.
        let ptr = unsafe { self.as_header() };

        //  Safety:
        //  -   Convertible: as per pre-condition.
        unsafe { &mut *ptr }
    }
}

//
//  Low-level Access
//

impl<T, H> ThinPtrWith<T, H>
where
    T: ?Sized,
{
    /// Returns a pointer to the data portion of `T`.
    #[inline(always)]
    pub const fn as_data(&self) -> *mut u8 {
        self.ptr
    }

    /// Returns a pointer to the header `H`.
    ///
    /// #   Safety
    ///
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with a header `H`.
    #[inline(always)]
    pub const unsafe fn as_header(&self) -> *mut H {
        let layout = Self::header_layout();

        let offset = layout.header_offset();

        //  Safety:
        //  -   InBounds: `layout.header_offset()` is within the memory block, as per the Suitable pre-condition.
        let header = unsafe { self.ptr.sub(offset) };

        header.cast()
    }

    /// Returns a pointer to the metadata.
    ///
    /// #   Safety
    ///
    /// -   Suitable: the thin memory block the pointer points to SHALL have been constructed with a header `H`.
    #[inline(always)]
    pub const unsafe fn as_metadata(&self) -> *const <T as Pointee>::Metadata {
        let layout = Self::header_layout();

        let offset = layout.metadata_offset();

        //  Safety:
        //  -   InBounds: `layout.metadata_offset()` is within the memory block, as per the Suitable pre-condition.
        let metadata = unsafe { self.ptr.sub(offset) };

        metadata.cast()
    }
}

//
//  Implementation
//

impl<T, H> ThinPtrWith<T, H> {
    #[inline(always)]
    pub(crate) const fn layout() -> ThinLayout {
        ThinLayout::new::<T, H, T, ()>()
    }
}

impl<T, H> ThinPtrWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    pub(crate) const fn header_layout() -> ThinLayout {
        ThinLayout::new::<(), H, T, ()>()
    }
}

//
//  Traits
//

impl<T, H> Clone for ThinPtrWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, H> Copy for ThinPtrWith<T, H> where T: ?Sized {}

impl<T, H> fmt::Debug for ThinPtrWith<T, H>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Pointer::fmt(&self.ptr, f)
    }
}

impl<T, H> fmt::Pointer for ThinPtrWith<T, H>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Pointer::fmt(&self.ptr, f)
    }
}

impl<T, H> Eq for ThinPtrWith<T, H> where T: ?Sized {}

impl<T, H> PartialEq for ThinPtrWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T, H> hash::Hash for ThinPtrWith<T, H>
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

impl<T, H> Ord for ThinPtrWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.ptr.cmp(&other.ptr)
    }
}

impl<T, H> PartialOrd for ThinPtrWith<T, H>
where
    T: ?Sized,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}
