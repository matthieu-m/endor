//! Thin pointers equivalent of `Rc<T>`.
//!
//! For the layout of these thin pointers, refer to the crate-level documentation, noting that there is _always_ a
//! an additional header for the reference count.

use core::{
    cell::Cell,
    cmp, convert, fmt, hash, hint,
    marker::Unsize,
    mem::{self, MaybeUninit},
    ops, panic,
    pin::Pin,
    ptr::NonNull,
};

use alloc::alloc::{AllocError, Allocator, Global};

use crate::{ThinNonNullWith, ThinRawWith};

/// The thin equivalent of `Rc<T, A = Global>`.
pub type ThinRc<T, A = Global> = ThinRcFlex<T, (), WithWeak, A>;

/// The thin equivalent of `Rc<T, A = Global>`, except that it only has a strong count.
pub type ThinRcLite<T, A = Global> = ThinRcFlex<T, (), StrongOnly, A>;

/// A `ThinRc` with a customizable header.
pub type ThinRcWith<T, H, A = Global> = ThinRcFlex<T, H, WithWeak, A>;

/// A `ThinRcLite` with a customizable header.
pub type ThinRcLiteWith<T, H, A = Global> = ThinRcFlex<T, H, StrongOnly, A>;

/// The thin equivalent of `Rc<T, A = Global>` (modulo Strong/Weak counts), with a header of the user's choice.
pub struct ThinRcFlex<T, H, RC, A = Global>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    inner: ThinRawWith<T, (H, RC), A>,
}

//
//  Conversion
//

impl<T, H, RC, A> ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    /// Constructs an instance from a raw pointer.
    ///
    /// #   Safety
    ///
    /// -   RoundTrip: `ptr` must have been obtained by a call to `Self::into_non_null`.
    #[inline(always)]
    pub unsafe fn from_non_null(ptr: ThinNonNullWith<T, (H, RC)>) -> Self {
        //  Safety:
        //  -   RoundTrip: as per pre-condition.
        let inner = unsafe { ThinRawWith::from_non_null(ptr) };

        Self { inner }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub fn into_non_null(this: Self) -> ThinNonNullWith<T, (H, RC)> {
        let inner = Self::into_raw(this);

        inner.into_non_null()
    }

    /// Converts a `Self` into a `Pin<Self>`.
    #[inline(always)]
    pub fn into_pin(this: Self) -> Pin<Self> {
        //  Safety:
        //  -   Pinned: single memory allocation, nothing will move.
        unsafe { Pin::new_unchecked(this) }
    }
}

impl<T, H, RC, A> ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    fn into_raw(this: Self) -> ThinRawWith<T, (H, RC), A> {
        let inner = this.inner;

        mem::forget(this);

        inner
    }
}

//
//  Construction
//

impl<T, RC> ThinRcFlex<T, (), RC, Global>
where
    RC: RefCount,
{
    /// Allocates memory on the heap and then places `value` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new` to handle failures gracefully.
    #[inline(always)]
    pub fn new(value: T) -> Self {
        Self::try_new(value).unwrap()
    }

    /// Attempts to allocate memory on the heap and then places `value` into it.
    ///
    /// Returns an error if the allocation fails. Use `new` for a panicking version instead.
    #[inline(always)]
    pub fn try_new(value: T) -> Result<Self, AllocError> {
        Self::try_new_in(value, Global)
    }
}

impl<U, RC> ThinRcFlex<U, (), RC, Global>
where
    U: ?Sized,
    RC: RefCount,
{
    /// Allocates memory on the heap and then places `value` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new` to handle failures gracefully.
    #[inline(always)]
    pub fn new_unsize<T>(value: T) -> Self
    where
        T: Unsize<U>,
    {
        Self::try_new_unsize(value).unwrap()
    }

    /// Attempts to allocate memory on the heap and then places `value` into it.
    ///
    /// Returns an error if the allocation fails. Use `new` for a panicking version instead.
    #[inline(always)]
    pub fn try_new_unsize<T>(value: T) -> Result<Self, AllocError>
    where
        T: Unsize<U>,
    {
        Self::try_new_unsize_in(value, Global)
    }
}

impl<T, H, RC> ThinRcFlex<T, H, RC, Global>
where
    RC: RefCount,
{
    /// Allocates memory on the heap and then places `value` and `header` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new_with` to handle failures gracefully.
    #[inline(always)]
    pub fn new_with(value: T, header: H) -> Self {
        Self::try_new_with(value, header).unwrap()
    }

    /// Attempts to allocate memory on the heap and then places `value` and `header` into it.
    ///
    /// Returns an error if the allocation fails. Use `new_with` for a panicking version instead.
    #[inline(always)]
    pub fn try_new_with(value: T, header: H) -> Result<Self, AllocError> {
        Self::try_new_with_in(value, header, Global)
    }
}

impl<U, H, RC> ThinRcFlex<U, H, RC, Global>
where
    U: ?Sized,
    RC: RefCount,
{
    /// Allocates memory on the heap and then places `value` and `header` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new_unsize_with` to handle failures gracefully.
    #[inline(always)]
    pub fn new_unsize_with<T>(value: T, header: H) -> Self
    where
        T: Unsize<U>,
    {
        Self::try_new_unsize_with(value, header).unwrap()
    }

    /// Attempts to allocate memory on the heap and then places `value` and `header` into it.
    ///
    /// Returns an error if the allocation fails. Use `new_with` for a panicking version instead.
    #[inline(always)]
    pub fn try_new_unsize_with<T>(value: T, header: H) -> Result<Self, AllocError>
    where
        T: Unsize<U>,
    {
        Self::try_new_unsize_with_in(value, header, Global)
    }
}

impl<T, RC, A> ThinRcFlex<T, (), RC, A>
where
    RC: RefCount,
    A: Allocator,
{
    /// Allocates memory with `allocator`, and then places `value` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new_in` to handle failures gracefully.
    #[inline(always)]
    pub fn new_in(value: T, allocator: A) -> Self {
        Self::try_new_in(value, allocator).unwrap()
    }

    /// Attempts to allocate memory with `allocator` and then places `value` into it.
    ///
    /// Returns an error if the allocation fails. Use `new_in` for a panicking version instead.
    #[inline(always)]
    pub fn try_new_in(value: T, allocator: A) -> Result<Self, AllocError> {
        Self::try_new_with_in(value, (), allocator)
    }
}

impl<U, RC, A> ThinRcFlex<U, (), RC, A>
where
    U: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    /// Allocates memory with `allocator`, and then places `value` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new_unsize_in` to handle failures gracefully.
    #[inline(always)]
    pub fn new_unsize_in<T>(value: T, allocator: A) -> Self
    where
        T: Unsize<U>,
    {
        Self::try_new_unsize_in(value, allocator).unwrap()
    }

    /// Attempts to allocate memory with `allocator` and then places `value` into it.
    ///
    /// Returns an error if the allocation fails. Use `new_unsize_in` for a panicking version instead.
    #[inline(always)]
    pub fn try_new_unsize_in<T>(value: T, allocator: A) -> Result<Self, AllocError>
    where
        T: Unsize<U>,
    {
        Self::try_new_unsize_with_in(value, (), allocator)
    }
}

impl<T, H, RC, A> ThinRcFlex<T, H, RC, A>
where
    RC: RefCount,
    A: Allocator,
{
    /// Allocates memory with `allocator`, and then places `value` and `header` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new_with_in` to handle failures gracefully.
    #[inline(always)]
    pub fn new_with_in(value: T, header: H, allocator: A) -> Self {
        Self::try_new_with_in(value, header, allocator).unwrap()
    }

    /// Attempts to allocate memory with `allocator` and then places `value` and `header` into it.
    ///
    /// Returns an error if the allocation fails. Use `new_in` for a panicking version instead.
    pub fn try_new_with_in(value: T, header: H, allocator: A) -> Result<Self, AllocError> {
        let header = (header, RC::new());

        ThinRawWith::try_new(value, header, allocator).map(|inner| Self { inner })
    }
}

impl<U, H, RC, A> ThinRcFlex<U, H, RC, A>
where
    U: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    /// Allocates memory with `allocator`, and then places `value` and `header` into it.
    ///
    /// #   Panics
    ///
    /// If there is not enough memory. Use `try_new_unsize_with_in` to handle failures gracefully.
    #[inline(always)]
    pub fn new_unsize_with_in<T>(value: T, header: H, allocator: A) -> Self
    where
        T: Unsize<U>,
    {
        Self::try_new_unsize_with_in(value, header, allocator).unwrap()
    }

    /// Attempts to allocate memory with `allocator` and then places `value` and `header` into it.
    ///
    /// Returns an error if the allocation fails. Use `new_in` for a panicking version instead.
    pub fn try_new_unsize_with_in<T>(value: T, header: H, allocator: A) -> Result<Self, AllocError>
    where
        T: Unsize<U>,
    {
        let header = (header, RC::new());

        ThinRawWith::try_new_unsize(value, header, allocator).map(|inner| Self { inner })
    }
}

impl<T, H, RC, A> Clone for ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    fn clone(&self) -> Self {
        let rc = self.as_ref_count();

        rc.increment_strong();

        Self { inner: self.inner }
    }
}

//
//  Destruction
//

impl<T, H, RC, A> Drop for ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    fn drop(&mut self) {
        let rc = self.as_ref_count();

        rc.decrement_strong();

        if rc.strong_count() != 0 {
            return;
        }

        //  Safety:
        //  -   EndOfStrong: strong count just reached 0.
        unsafe { self.destruct() };
    }
}

impl<T, H, RC, A> ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    //  #   Safety
    //
    //  -   EndOfStrong: strong count must JUST have reached 0.
    unsafe fn destruct(&mut self) {
        let rc = self.as_ref_count();
        let weak = rc.weak_count();

        debug_assert_eq!(0, rc.strong_count());

        //  Safety:
        //  -   Droppable: the strong count JUST reached 0, hence value & header are alive and well.
        unsafe { self.inner.drop_in_place() };

        if weak != 0 {
            return;
        }

        //  Safety:
        //  -   EndOfLife: per Accounting.
        let _ = unsafe { self.inner.drop_guard() };
    }
}

//
//  High-level Access
//

impl<T, H, RC, A> ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    /// Returns a reference to the data.
    #[inline(always)]
    pub const fn as_ref(this: &Self) -> &T {
        //  Safety:
        //  -   Convertible: alive & guarded shared access.
        unsafe { this.inner.as_ref() }
    }

    /// Returns a reference to `H`.
    #[inline(always)]
    pub const fn as_header_ref(this: &Self) -> &H {
        //  Safety:
        //  -   Convertible: alive & guarded shared access.
        unsafe { &this.inner.as_header_ref().0 }
    }
}

//
//  Low-level Access
//

impl<T, H, RC, A> ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub const fn as_non_null(&self) -> ThinNonNullWith<T, (H, RC)> {
        self.inner.as_non_null()
    }

    /// Returns a pointer to the allocator.
    ///
    /// The pointer MAY NOT be suitably aligned for `A`.
    #[inline(always)]
    pub const fn as_allocator(this: &Self) -> NonNull<A> {
        this.inner.as_allocator()
    }
}

//
//  Value Access
//

impl<T, H, RC, A> convert::AsRef<T> for ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    fn as_ref(&self) -> &T {
        Self::as_ref(self)
    }
}

impl<T, H, RC, A> ops::Deref for ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    type Target = T;

    fn deref(&self) -> &T {
        Self::as_ref(self)
    }
}

//
//  Implementation
//

impl<T, H, RC, A> ThinRcFlex<T, H, RC, A>
where
    T: ?Sized,
    RC: RefCount,
    A: Allocator,
{
    fn as_ref_count(&self) -> &RC {
        //  Safety:
        //  -   Suitable: per invariant.
        let header = unsafe { self.inner.as_header_ref() };

        &header.1
    }
}

//
//  Customizable reference counts.
//

mod sealed {
    //  Lie: it's not reexported.
    pub trait Sealed {}
}

//  Only intended for use within the library.
//
//  The weak count is the number of weak references + 1 if there is any strong reference.
//
//  #   Safety
//
//  -   Accounting: the strong & weak counts are properly maintained.
#[doc(hidden)]
pub unsafe trait RefCount: sealed::Sealed {
    /// Constructs a reference counted header.
    ///
    /// A freshly constructed header has a strong & weak counts of exactly 1.
    fn new() -> Self;

    /// Increments the strong count.
    fn increment_strong(&self);

    /// Decrements the strong count.
    fn decrement_strong(&self);

    /// Returns the strong count.
    ///
    /// On 0, the data is dropped.
    fn strong_count(&self) -> u64;

    /// Returns the weak count.
    ///
    /// On 0, the memory block is deallocated.
    fn weak_count(&self) -> u64;
}

/// Only a strong reference count.
#[derive(Debug)]
pub struct StrongOnly {
    strong: Cell<u64>,
}

impl sealed::Sealed for StrongOnly {}

//  Safety:
//  -   Accounting: properly counted.
unsafe impl RefCount for StrongOnly {
    #[inline(always)]
    fn new() -> Self {
        let strong = Cell::new(1);

        Self { strong }
    }

    #[inline(always)]
    fn increment_strong(&self) {
        self.strong.update(|c| c + 1);
    }

    #[inline(always)]
    fn decrement_strong(&self) {
        self.strong.update(|c| c - 1);
    }

    #[inline(always)]
    fn strong_count(&self) -> u64 {
        self.strong.get()
    }

    #[inline(always)]
    fn weak_count(&self) -> u64 {
        self.strong.get()
    }
}

/// Both a strong and a weak reference counts.
#[derive(Debug)]
pub struct WithWeak {
    strong: Cell<u64>,
    weak: Cell<u64>,
}

impl WithWeak {
    #[inline(always)]
    fn increment_weak(&self) {
        self.weak.update(|c| c + 1);
    }

    #[inline(always)]
    fn decrement_weak(&self) {
        self.weak.update(|c| c - 1);
    }
}

impl sealed::Sealed for WithWeak {}

//  Safety:
//  -   Accounting: properly counted.
unsafe impl RefCount for WithWeak {
    #[inline(always)]
    fn new() -> Self {
        let strong = Cell::new(1);
        let weak = Cell::new(1);

        Self { strong, weak }
    }

    #[inline(always)]
    fn increment_strong(&self) {
        self.strong.update(|c| c + 1);
    }

    #[inline]
    fn decrement_strong(&self) {
        self.strong.update(|c| c - 1);

        if self.strong.get() == 0 {
            self.decrement_weak();
        }
    }

    #[inline(always)]
    fn strong_count(&self) -> u64 {
        self.strong.get()
    }

    #[inline(always)]
    fn weak_count(&self) -> u64 {
        self.weak.get()
    }
}
