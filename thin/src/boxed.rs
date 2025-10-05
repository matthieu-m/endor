//! Thin pointers equivalent of `Box<T>`.
//!
//! For the layout of these thin pointers, refer to the crate-level documentation.

use core::{
    cmp, convert, fmt, hash,
    marker::Unsize,
    mem::{self, MaybeUninit},
    ops, panic,
};

use alloc::alloc::{AllocError, Allocator, Global};

use crate::{ThinNonNullWith, ThinRawWith};

/// The thin equivalent of `Box<T, A = Global>`.
pub type ThinBox<T, A = Global> = ThinBoxWith<T, (), A>;

/// The thin equivalent of `Box<T, A = Global>`, with a header of the user's choice.
pub struct ThinBoxWith<T, H, A = Global>
where
    T: ?Sized,
    A: Allocator,
{
    inner: ThinRawWith<T, H, A>,
}

//
//  Conversion
//

impl<T, H, A> ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Constructs an instance from a raw pointer.
    ///
    /// #   Safety
    ///
    /// -   RoundTrip: `ptr` must have been obtained by a call to `Self::into_raw`.
    #[inline(always)]
    pub unsafe fn from_raw(ptr: ThinNonNullWith<T, H>) -> Self {
        //  Safety:
        //  -   RoundTrip: as per pre-condition.
        let inner = unsafe { ThinRawWith::from_raw(ptr) };

        Self { inner }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub fn into_raw(self) -> ThinNonNullWith<T, H> {
        self.inner.into_raw()
    }
}

impl<T, H, A> ThinBoxWith<T, H, A>
where
    A: Allocator,
{
    /// Consumes the box without consuming its allocation.
    #[inline]
    pub fn take(this: Self) -> (T, H, ThinBoxWith<MaybeUninit<T>, MaybeUninit<H>, A>) {
        //  Safety:
        //  -   `EndOfLife`: `this` will no longer be used as is.
        let (value, header, inner) = unsafe { ThinRawWith::take(this.inner) };

        //  Don't drop it!
        mem::forget(this);

        (value, header, ThinBoxWith { inner })
    }
}

impl<T, H, A> ThinBoxWith<MaybeUninit<T>, MaybeUninit<H>, A>
where
    A: Allocator,
{
    /// Converts to `ThinBoxWith<T, H, A>`.
    ///
    /// #   Safety
    ///
    /// -   Initialized: as per `MaybeUninit::assume_init`.
    #[inline(always)]
    pub unsafe fn assume_init(this: Self) -> ThinBoxWith<T, H, A> {
        //  Safety:
        //  -   Initialized: as per pre-condition.
        let inner = unsafe { ThinRawWith::assume_init(this.inner) };

        mem::forget(this);

        ThinBoxWith { inner }
    }

    /// Initializes the uninitialized parts of `self`.
    #[inline]
    pub fn write(this: Self, value: T, header: H) -> ThinBoxWith<T, H, A> {
        //  Safety:
        //  -   Mutable: no other instance of the box can be used simultaneously.
        let inner = unsafe { ThinRawWith::write(this.inner, value, header) };

        mem::forget(this);

        ThinBoxWith { inner }
    }
}

//
//  Construction
//

impl<T> ThinBoxWith<T, (), Global> {
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

impl<U> ThinBoxWith<U, (), Global>
where
    U: ?Sized,
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

impl<T, H> ThinBoxWith<T, H, Global> {
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

impl<U, H> ThinBoxWith<U, H, Global>
where
    U: ?Sized,
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

impl<T, A> ThinBoxWith<T, (), A>
where
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

impl<U, A> ThinBoxWith<U, (), A>
where
    U: ?Sized,
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

impl<T, H, A> ThinBoxWith<T, H, A>
where
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
        ThinRawWith::try_new(value, header, allocator).map(|inner| Self { inner })
    }
}

impl<U, H, A> ThinBoxWith<U, H, A>
where
    U: ?Sized,
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
        ThinRawWith::try_new_unsize(value, header, allocator).map(|inner| Self { inner })
    }
}

//
//  Destruction
//

impl<T, H, A> Drop for ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn drop(&mut self) {
        //  Safety:
        //  -   EndOfLife: last use of `self.inner`.
        unsafe { self.inner.drop() };
    }
}

//
//  High-level Access
//

impl<T, H, A> ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub const fn as_ptr(&self) -> ThinNonNullWith<T, H> {
        self.inner.as_ptr()
    }

    /// Returns a reference to the data.
    #[inline(always)]
    pub const fn as_ref(&self) -> &T {
        //  Safety:
        //  -   Convertible: alive & guarded shared access.
        unsafe { self.inner.as_ref() }
    }

    /// Returns a reference to the data.
    #[inline(always)]
    pub const fn as_mut(&mut self) -> &mut T {
        //  Safety:
        //  -   Convertible: alive & guarded exclusive access.
        unsafe { self.inner.as_mut() }
    }

    /// Returns a reference to `H`.
    #[inline(always)]
    pub const fn as_header_ref(&self) -> &H {
        //  Safety:
        //  -   Convertible: alive & guarded shared access.
        unsafe { self.inner.as_header_ref() }
    }

    /// Returns a mutable reference to `H`.
    #[inline(always)]
    pub const fn as_header_mut(&mut self) -> &mut H {
        //  Safety:
        //  -   Convertible: alive & guarded exclusive access.
        unsafe { self.inner.as_header_mut() }
    }
}

//
//  Value Access
//

impl<T, H, A> convert::AsRef<T> for ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn as_ref(&self) -> &T {
        self.as_ref()
    }
}

impl<T, H, A> convert::AsMut<T> for ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn as_mut(&mut self) -> &mut T {
        self.as_mut()
    }
}

impl<T, H, A> ops::Deref for ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    type Target = T;

    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T, H, A> ops::DerefMut for ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn deref_mut(&mut self) -> &mut T {
        self.as_mut()
    }
}

//
//  Formatting
//

impl<T, H, A> fmt::Debug for ThinBoxWith<T, H, A>
where
    T: ?Sized + fmt::Debug,
    H: fmt::Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ThinBoxWith")
            .field("header", self.as_header_ref())
            .field("value", &self.as_ref())
            .finish()
    }
}

impl<T, H, A> fmt::Display for ThinBoxWith<T, H, A>
where
    T: ?Sized + fmt::Display,
    A: Allocator,
{
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(&self.as_ref(), f)
    }
}

//
//  Identity
//

impl<T, H, A> Eq for ThinBoxWith<T, H, A>
where
    T: ?Sized + Eq,
    A: Allocator,
{
}

impl<T, H, A> PartialEq for ThinBoxWith<T, H, A>
where
    T: ?Sized + PartialEq,
    A: Allocator,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.as_ref().eq(other.as_ref())
    }
}

impl<T, H, A> hash::Hash for ThinBoxWith<T, H, A>
where
    T: ?Sized + hash::Hash,
    A: Allocator,
{
    #[inline(always)]
    fn hash<HS>(&self, hasher: &mut HS)
    where
        HS: hash::Hasher,
    {
        self.as_ref().hash(hasher);
    }
}

//
//  Ordering
//

impl<T, H, A> Ord for ThinBoxWith<T, H, A>
where
    T: ?Sized + Ord,
    A: Allocator,
{
    #[inline(always)]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl<T, H, A> PartialOrd for ThinBoxWith<T, H, A>
where
    T: ?Sized + PartialOrd,
    A: Allocator,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

//
//  Markers
//

//  Safety: as Box.
impl<T, H, A> Unpin for ThinBoxWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
}

//  Safety: as Box.
impl<T, H, A> panic::RefUnwindSafe for ThinBoxWith<T, H, A>
where
    T: ?Sized + panic::RefUnwindSafe,
    H: panic::RefUnwindSafe,
    A: Allocator + panic::RefUnwindSafe,
{
}

//  Safety: as Box.
impl<T, H, A> panic::UnwindSafe for ThinBoxWith<T, H, A>
where
    T: ?Sized + panic::UnwindSafe,
    H: panic::UnwindSafe,
    A: Allocator + panic::UnwindSafe,
{
}

//  Safety: as Box.
unsafe impl<T, H, A> Send for ThinBoxWith<T, H, A>
where
    T: ?Sized + Send,
    H: Send,
    A: Allocator + Send,
{
}

//  Safety: as Box.
unsafe impl<T, H, A> Sync for ThinBoxWith<T, H, A>
where
    T: ?Sized + Sync,
    H: Sync,
    A: Allocator + Sync,
{
}
