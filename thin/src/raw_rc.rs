//! Handles the actual memory finnicky details of reference counting.

use core::{fmt, marker::Unsize, panic, ptr::NonNull};

use alloc::alloc::{AllocError, Allocator};

use crate::{ThinNonNullWith, ThinRawWith};

/// The header of a reference counted thin pointer.
pub struct ThinRefCountHeader<H, RF> {
    header: H,
    count: RF,
}

impl<H, RF> ThinRefCountHeader<H, RF> {
    /// Returns the header.
    pub fn header(&self) -> &H {
        &self.header
    }
}

impl<H, RF> fmt::Debug for ThinRefCountHeader<H, RF>
where
    H: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Debug::fmt(&self.header, f)
    }
}

/// A reference count with a strong and weak counts.
///
/// The strong count represents the number of "strong" handles to the objects, ie the number of instances of
/// `ThinRawRcWith`. The objects are dropped (in place) when the strong count reaches 0.
///
/// The weak count represents the number of "weak" handles to the memory block, ie the number of instances of
/// `ThinRawWeakWith` + 1 if any instance of `ThinRawRcWith` exists. The memory block is deallocated when the weak count
/// reaches 0.
///
/// #   Safety
///
/// -   Accounting: the strong & weak counts are properly maintained, and the appropriate operations (drop, deallocate)
///     are invoked at the appropriate time.
pub(crate) unsafe trait ThinRefCount {
    /// Constructs a reference counted header.
    ///
    /// A freshly constructed header has a strong & weak counts of exactly 1.
    fn new() -> Self;

    /// Returns the strong count, ie the number of strong handles.
    ///
    /// On 0, the data is dropped.
    fn strong_count(&self) -> u64;

    /// Increments the strong count.
    ///
    /// #   Safety
    ///
    /// -   Accounting: the caller guarantees that the incremented count faithfully represent the number of strong
    ///     handles.
    unsafe fn increment_strong(&self);

    /// Decrements the strong count.
    ///
    /// #   Safety
    ///
    /// -   Accounting: the caller guarantees that the decremented count faithfully represent the number of strong
    ///     handles.
    unsafe fn decrement_strong<D, DA>(&self, drop: D, deallocate: DA)
    where
        D: FnOnce(),
        DA: FnOnce();
}

/// The weak part of the ref count.
///
/// #   Safety
///
/// -   Accounting: as per `ThinRefCount`.
pub(crate) unsafe trait ThinWeakCount: ThinRefCount {
    /// Returns the weak count, ie the number of weak handles + 1 if any strong handle exists.
    ///
    /// On 0, the memory block is deallocated.
    fn weak_count(&self) -> u64;

    /// Tries to increment the strong count, unless it is already zero.
    ///
    /// Returns whether the increment succeeded.
    unsafe fn try_increment_strong(&self) -> bool;

    /// Increments the weak count.
    ///
    /// #   Safety
    ///
    /// -   Accounting: the caller guarantees that the incremented count faithfully represent the number of weak
    ///     handles.
    unsafe fn increment_weak(&self);

    /// Decrements the weak count.
    ///
    /// #   Safety
    ///
    /// -   Accounting: the caller guarantees that the decremented count faithfully represent the number of weak
    ///     handles.
    unsafe fn decrement_weak<DA>(&self, deallocate: DA)
    where
        DA: FnOnce();
}

/// Generic reference-counted raw handle, equivalent to Rc/Arc.
#[repr(transparent)]
pub(crate) struct ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    raw: ThinRawWith<T, ThinRefCountHeader<H, RF>, A>,
}

/// Generic reference-counted raw handle, equivalent to Weak.
#[repr(transparent)]
pub(crate) struct ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    raw: ThinRawWith<T, ThinRefCountHeader<H, RF>, A>,
}

//
//  Conversions
//

impl<T, H, RF, A> ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    /// Constructs an instance from a raw pointer.
    ///
    /// #   Safety
    ///
    /// -   RoundTrip: `ptr` must have been obtained by a call to `Self::into_non_null`.
    #[inline(always)]
    pub(crate) unsafe fn from_non_null(ptr: ThinNonNullWith<T, ThinRefCountHeader<H, RF>>) -> Self {
        //  Safety:
        //  -   RoundTrip: per pre-condition.
        let raw = unsafe { ThinRawWith::from_non_null(ptr) };

        Self { raw }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub(crate) fn into_non_null(self) -> ThinNonNullWith<T, ThinRefCountHeader<H, RF>> {
        self.raw.into_non_null()
    }
}

impl<T, H, RF, A> ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    /// Constructs an instance from a raw pointer.
    ///
    /// #   Safety
    ///
    /// -   RoundTrip: `ptr` must have been obtained by a call to `Self::into_non_null`.
    #[inline(always)]
    pub(crate) unsafe fn from_non_null(ptr: ThinNonNullWith<T, ThinRefCountHeader<H, RF>>) -> Self {
        //  Safety:
        //  -   RoundTrip: per pre-condition.
        let raw = unsafe { ThinRawWith::from_non_null(ptr) };

        Self { raw }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub(crate) fn into_non_null(self) -> ThinNonNullWith<T, ThinRefCountHeader<H, RF>> {
        self.raw.into_non_null()
    }
}

//
//  Construction
//

impl<T, H, RF, A> ThinRawRcWith<T, H, RF, A>
where
    RF: ThinRefCount,
    A: Allocator,
{
    /// Attempts to allocate, if necessary, moves the `value`, `header`, and `allocator` in, and returns an instance.
    #[inline(always)]
    pub(crate) fn try_new(value: T, header: H, allocator: A) -> Result<Self, AllocError> {
        let count = RF::new();

        debug_assert_eq!(1, count.strong_count());

        let raw = ThinRawWith::try_new(value, ThinRefCountHeader { header, count }, allocator)?;

        Ok(Self { raw })
    }
}

impl<U, H, RF, A> ThinRawRcWith<U, H, RF, A>
where
    U: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    /// Attempts to allocate, if necessary, moves the `value`, `header`, and `allocator` in, and returns an instance.
    #[inline(always)]
    pub(crate) fn try_new_unsize<T>(value: T, header: H, allocator: A) -> Result<Self, AllocError>
    where
        T: Unsize<U>,
    {
        let count = RF::new();

        debug_assert_eq!(1, count.strong_count());

        let raw = ThinRawWith::try_new_unsize(value, ThinRefCountHeader { header, count }, allocator)?;

        Ok(Self { raw })
    }
}

impl<T, H, RF, A> ThinRawRcWith<T, H, RF, A>
where
    RF: ThinWeakCount,
    A: Allocator,
{
    /// Constructs a new `ThinRawWeakWith` pointer to this allocation.
    #[inline(always)]
    pub(crate) fn downgrade(this: &Self) -> ThinRawWeakWith<T, H, RF, A> {
        //  Safety:
        //  -   Lifetime: the weak count will not reach 0.
        let count = unsafe { this.count() };

        //  Safety:
        //  -   Accounting: the number of weak handles is increased by one.
        unsafe { count.increment_weak() };

        ThinRawWeakWith { raw: this.raw }
    }
}

impl<T, H, RF, A> ThinRawWeakWith<T, H, RF, A>
where
    RF: ThinWeakCount,
    A: Allocator,
{
    /// Attempts to upgrade the `ThinRawWeakWith` pointer to a `ThinRawRcWith`.
    ///
    /// Returns `None` if the inner value has already been dropped.
    #[inline(always)]
    pub(crate) fn upgrade(this: &Self) -> Option<ThinRawRcWith<T, H, RF, A>> {
        //  Safety:
        //  -   Lifetime: the weak count will not reach 0.
        let count = unsafe { this.count() };

        //  Safety:
        //  -   Accounting: the number of strong handles is increased by one on success.
        let upgraded = unsafe { count.try_increment_strong() };

        upgraded.then(|| ThinRawRcWith { raw: this.raw })
    }
}

//
//  Destruction
//

impl<T, H, RF, A> Drop for ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    fn drop(&mut self) {
        //  Safety:
        //  -   Lifetime: the resulting reference will not be used after calling `decrement_strong`.
        let count = unsafe { self.count() };

        debug_assert!(count.strong_count() > 0);

        let mut raw = self.raw;

        //  Safety:
        //  -   Droppable: the objects have been "alive" until now, since the strong count was > 0.
        //  -   EndOfLife: the objects will no longer be accessed, since this was the last strong handle.
        let drop = move || unsafe { raw.drop_in_place() };

        //  Safety:
        //  -   EndOfLife: the memory block will no longer be accessed, since this was the last handle.
        let deallocate = move || unsafe {
            let _ = raw.drop_guard();
        };

        //  Safety:
        //  -   Accounting: one less strong instance exists after `drop`.
        unsafe { count.decrement_strong(drop, deallocate) };
    }
}

impl<T, H, RF, A> Drop for ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    fn drop(&mut self) {
        //  Safety:
        //  -   Lifetime: the resulting reference will not be used after calling `decrement_weak`.
        let count = unsafe { self.count() };

        debug_assert!(count.weak_count() > 0);

        let mut raw = self.raw;

        //  Safety:
        //  -   EndOfLife: the memory block will no longer be accessed, since this was the last handle.
        let deallocate = move || unsafe {
            let _ = raw.drop_guard();
        };

        //  Safety:
        //  -   Accounting: one less weak instance exists after `drop`.
        unsafe { count.decrement_weak(deallocate) };
    }
}

//
//  High-level Access
//

impl<T, H, RF, A> ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    /// Returns the number of strong handles, ie `ThinRawRcWith`.
    #[inline(always)]
    pub fn strong_count(&self) -> u64 {
        //  Safety:
        //  -   Lifetime: this handles guarantees that the count is alive, and will remain so as long this handle
        //      is borrowed.
        unsafe { self.count().strong_count() }
    }

    /// Returns a reference to the data.
    #[inline(always)]
    pub(crate) const fn as_ref(&self) -> &T {
        //  Safety:
        //  -   Convertible: this handles guarantees that the value is alive, and will remain so as long this handle
        //      is borrowed.
        unsafe { self.raw.as_ref() }
    }

    /// Returns a reference to `H`.
    #[inline(always)]
    pub(crate) const fn as_header_ref(&self) -> &H {
        //  Safety:
        //  -   Convertible: this handles guarantees that the header is alive, and will remain so as long this handle
        //      is borrowed.
        unsafe { &self.raw.as_header_ref().header }
    }
}

impl<T, H, RF, A> ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    /// Returns the number of weak handles, ie `ThinRawWeakWith`, + 1 if any strong handle is alive.
    #[inline(always)]
    pub fn weak_count(&self) -> u64 {
        //  Safety:
        //  -   Lifetime: this handles guarantees that the count is alive, and will remain so as long this handle
        //      is borrowed.
        unsafe { self.count().weak_count() }
    }
}

impl<T, H, RF, A> ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    /// Returns the number of strong handles, ie `ThinRawRcWith`.
    #[inline(always)]
    pub fn strong_count(&self) -> u64 {
        //  Safety:
        //  -   Lifetime: this handles guarantees that the count is alive, and will remain so as long this handle
        //      is borrowed.
        unsafe { self.count().strong_count() }
    }

    /// Returns the number of weak handles, ie `ThinRawWeakWith`, + 1 if any strong handle is alive.
    #[inline(always)]
    pub fn weak_count(&self) -> u64 {
        //  Safety:
        //  -   Lifetime: this handles guarantees that the count is alive, and will remain so as long this handle
        //      is borrowed.
        unsafe { self.count().weak_count() }
    }
}

//
//  Low-level Access
//

impl<T, H, RF, A> ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub(crate) const fn as_non_null(&self) -> ThinNonNullWith<T, ThinRefCountHeader<H, RF>> {
        self.raw.as_non_null()
    }

    /// Returns a pointer to the allocator.
    ///
    /// The pointer MAY NOT be suitably aligned for `A`.
    #[inline(always)]
    pub(crate) const fn as_allocator(&self) -> NonNull<A> {
        self.raw.as_allocator()
    }
}

impl<T, H, RF, A> ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub(crate) const fn as_non_null(&self) -> ThinNonNullWith<T, ThinRefCountHeader<H, RF>> {
        self.raw.as_non_null()
    }

    /// Returns a pointer to the allocator.
    ///
    /// The pointer MAY NOT be suitably aligned for `A`.
    #[inline(always)]
    pub(crate) const fn as_allocator(&self) -> NonNull<A> {
        self.raw.as_allocator()
    }
}

//
//  Clone
//

impl<T, H, RF, A> Clone for ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    fn clone(&self) -> Self {
        //  Safety:
        //  -   Lifetime: the weak count will not reach 0.
        let count = unsafe { self.count() };

        //  Safety:
        //  -   Accounting: the number of strong handles is increased by one.
        unsafe { count.increment_strong() };

        Self { raw: self.raw }
    }
}

impl<T, H, RF, A> Clone for ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    fn clone(&self) -> Self {
        //  Safety:
        //  -   Lifetime: the weak count will not reach 0.
        let count = unsafe { self.count() };

        //  Safety:
        //  -   Accounting: the number of weak handles is increased by one.
        unsafe { count.increment_weak() };

        Self { raw: self.raw }
    }
}

//
//  Marker traits
//

impl<T, H, RF, A> panic::RefUnwindSafe for ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
}

impl<T, H, RF, A> panic::RefUnwindSafe for ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
}

impl<T, H, RF, A> panic::UnwindSafe for ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
}

impl<T, H, RF, A> panic::UnwindSafe for ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
}

//  Safety: as Box.
unsafe impl<T, H, RF, A> Send for ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized + Send,
    H: Send,
    RF: ThinRefCount + Send,
    A: Allocator + Send,
{
}

//  Safety: as Box.
unsafe impl<T, H, RF, A> Send for ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized + Send,
    H: Send,
    RF: ThinWeakCount + Send,
    A: Allocator + Send,
{
}

//  Safety: as Box.
unsafe impl<T, H, RF, A> Sync for ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized + Sync,
    H: Sync,
    RF: ThinRefCount + Sync,
    A: Allocator + Sync,
{
}

//  Safety: as Box.
unsafe impl<T, H, RF, A> Sync for ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized + Sync,
    H: Sync,
    RF: ThinWeakCount + Sync,
    A: Allocator + Sync,
{
}

//
//  Implementation
//

impl<T, H, RF, A> ThinRawRcWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinRefCount,
    A: Allocator,
{
    //  Safety:
    //  -   Lifetime: the lifetime of the returned reference is only guaranteed until the its weak count reaches 0.
    unsafe fn count(&self) -> &RF {
        //  Safety:
        //  -   Convertible: as per pre-condition.
        unsafe { &self.raw.as_header_ref().count }
    }
}

impl<T, H, RF, A> ThinRawWeakWith<T, H, RF, A>
where
    T: ?Sized,
    RF: ThinWeakCount,
    A: Allocator,
{
    //  Safety:
    //  -   Lifetime: the lifetime of the returned reference is only guaranteed until the its weak count reaches 0.
    unsafe fn count(&self) -> &RF {
        //  Safety:
        //  -   Convertible: as per pre-condition.
        unsafe { &self.raw.as_header_ref().count }
    }
}
