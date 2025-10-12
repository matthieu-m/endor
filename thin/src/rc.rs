//! Thin pointers equivalent of `Rc<T>`.
//!
//! For the layout of these thin pointers, refer to the crate-level documentation, noting that there is _always_ a
//! an additional header for the reference count.

use core::{cell::Cell, cmp, convert, fmt, hash, marker::Unsize, mem::ManuallyDrop, ops, pin::Pin, ptr::NonNull};

use alloc::alloc::{AllocError, Allocator, Global};

use crate::{ThinNonNullWith, ThinRawRcWith, ThinRawWeakWith, ThinRefCount, ThinRefCountHeader, ThinWeakCount};

/// The thin equivalent of `Rc<T, A = Global>`.
pub type ThinRc<T, A = Global> = ThinRcWith<T, (), A>;

/// The thin equvialent of `Weak<T, A = Global>`.
pub type ThinWeak<T, A = Global> = ThinWeakWith<T, (), A>;

/// The header used by `ThinRcWith`.
pub type ThinRcHeader<H> = ThinRefCountHeader<H, ThinRcCount>;

/// The thin equivalent of `Rc<T, A = Global>`, with a header of the user's choice.
pub struct ThinRcWith<T, H, A = Global>
where
    T: ?Sized,
    A: Allocator,
{
    inner: ThinRawRcWith<T, H, ThinRcCount, A>,
}

/// The thin equivalent of `Weak<T, A = Global>`, with a header of the user's choice.
pub struct ThinWeakWith<T, H, A = Global>
where
    T: ?Sized,
    A: Allocator,
{
    inner: ThinRawWeakWith<T, H, ThinRcCount, A>,
}

//
//  Conversion
//

impl<T, H, A> ThinRcWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Constructs an instance from a raw pointer.
    ///
    /// #   Safety
    ///
    /// -   RoundTrip: `ptr` must have been obtained by a call to `Self::into_non_null`.
    #[inline(always)]
    pub unsafe fn from_non_null(ptr: ThinNonNullWith<T, ThinRcHeader<H>>) -> Self {
        //  Safety:
        //  -   RoundTrip: as per pre-condition.
        let inner = unsafe { ThinRawRcWith::from_non_null(ptr) };

        Self { inner }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub fn into_non_null(this: Self) -> ThinNonNullWith<T, ThinRcHeader<H>> {
        this.inner.into_non_null()
    }

    /// Converts a `Self` into a `Pin<Self>`.
    #[inline(always)]
    pub fn into_pin(this: Self) -> Pin<Self> {
        //  Safety:
        //  -   Pinned: single memory allocation, nothing will move.
        unsafe { Pin::new_unchecked(this) }
    }
}

impl<T, H, A> ThinWeakWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Constructs an instance from a raw pointer.
    ///
    /// #   Safety
    ///
    /// -   RoundTrip: `ptr` must have been obtained by a call to `Self::into_non_null`.
    #[inline(always)]
    pub unsafe fn from_non_null(ptr: ThinNonNullWith<T, ThinRcHeader<H>>) -> Self {
        //  Safety:
        //  -   RoundTrip: as per pre-condition.
        let inner = unsafe { ThinRawWeakWith::from_non_null(ptr) };

        Self { inner }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub fn into_non_null(this: Self) -> ThinNonNullWith<T, ThinRcHeader<H>> {
        this.inner.into_non_null()
    }
}

//
//  Construction
//

impl<T> ThinRcWith<T, (), Global> {
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

impl<U> ThinRcWith<U, (), Global>
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

impl<T, H> ThinRcWith<T, H, Global> {
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

impl<U, H> ThinRcWith<U, H, Global>
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

impl<T, A> ThinRcWith<T, (), A>
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

impl<U, A> ThinRcWith<U, (), A>
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

impl<T, H, A> ThinRcWith<T, H, A>
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
        ThinRawRcWith::try_new(value, header, allocator).map(|inner| Self { inner })
    }
}

impl<U, H, A> ThinRcWith<U, H, A>
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
        ThinRawRcWith::try_new_unsize(value, header, allocator).map(|inner| Self { inner })
    }
}

impl<T, H, A> ThinRcWith<T, H, A>
where
    A: Allocator,
{
    /// Constructs a new `ThinWeakWith` pointer to this allocation.
    pub fn downgrade(this: &Self) -> ThinWeakWith<T, H, A> {
        let inner = ThinRawRcWith::downgrade(&this.inner);

        ThinWeakWith { inner }
    }
}

impl<T, H, A> ThinWeakWith<T, H, A>
where
    A: Allocator,
{
    /// Attempts to upgrade the `ThinRawWeakWith` pointer to a `ThinRawRcWith`.
    ///
    /// Returns `None` if the inner value has already been dropped.
    pub fn upgrade(this: &Self) -> Option<ThinRcWith<T, H, A>> {
        ThinRawWeakWith::upgrade(&this.inner).map(|inner| ThinRcWith { inner })
    }
}

impl<T, H, A> Clone for ThinRcWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn clone(&self) -> Self {
        let inner = self.inner.clone();

        Self { inner }
    }
}

impl<T, H, A> Clone for ThinWeakWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn clone(&self) -> Self {
        let inner = self.inner.clone();

        Self { inner }
    }
}

//
//  High-level Access
//

impl<T, H, A> ThinRcWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns the number of strong handles, ie `ThinRcWith`.
    #[inline(always)]
    pub fn strong_count(this: &Self) -> u64 {
        this.inner.strong_count()
    }

    /// Returns the number of weak handles, ie `ThinWeakWith`, + 1 if any strong handle is alive.
    #[inline(always)]
    pub fn weak_count(this: &Self) -> u64 {
        this.inner.weak_count()
    }

    /// Returns a reference to the data.
    #[inline(always)]
    pub const fn as_ref(this: &Self) -> &T {
        this.inner.as_ref()
    }

    /// Returns a reference to `H`.
    #[inline(always)]
    pub const fn as_header_ref(this: &Self) -> &H {
        this.inner.as_header_ref()
    }
}

impl<T, H, A> ThinWeakWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns the number of strong handles, ie `ThinRcWith`.
    #[inline(always)]
    pub fn strong_count(this: &Self) -> u64 {
        this.inner.strong_count()
    }

    /// Returns the number of weak handles, ie `ThinWeakWith`, + 1 if any strong handle is alive.
    #[inline(always)]
    pub fn weak_count(this: &Self) -> u64 {
        this.inner.weak_count()
    }
}

//
//  Low-level Access
//

impl<T, H, A> ThinRcWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub const fn as_non_null(this: &Self) -> ThinNonNullWith<T, ThinRcHeader<H>> {
        this.inner.as_non_null()
    }

    /// Returns a pointer to the allocator.
    ///
    /// The pointer MAY NOT be suitably aligned for `A`.
    #[inline(always)]
    pub const fn as_allocator(this: &Self) -> NonNull<A> {
        this.inner.as_allocator()
    }
}

impl<T, H, A> ThinWeakWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub const fn as_non_null(this: &Self) -> ThinNonNullWith<T, ThinRcHeader<H>> {
        this.inner.as_non_null()
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

impl<T, H, A> convert::AsRef<T> for ThinRcWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn as_ref(&self) -> &T {
        Self::as_ref(self)
    }
}

impl<T, H, A> ops::Deref for ThinRcWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    type Target = T;

    fn deref(&self) -> &T {
        Self::as_ref(self)
    }
}

//
//  Formatting
//

impl<T, H, A> fmt::Debug for ThinRcWith<T, H, A>
where
    T: ?Sized + fmt::Debug,
    H: fmt::Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ThinRcWith")
            .field("header", Self::as_header_ref(self))
            .field("value", &Self::as_ref(self))
            .finish()
    }
}

impl<T, H, A> fmt::Display for ThinRcWith<T, H, A>
where
    T: ?Sized + fmt::Display,
    A: Allocator,
{
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(&Self::as_ref(self), f)
    }
}

//
//  Identity
//

impl<T, H, A> Eq for ThinRcWith<T, H, A>
where
    T: ?Sized + Eq,
    A: Allocator,
{
}

impl<T, H, A> PartialEq for ThinRcWith<T, H, A>
where
    T: ?Sized + PartialEq,
    A: Allocator,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        Self::as_ref(self).eq(Self::as_ref(other))
    }
}

impl<T, H, A> hash::Hash for ThinRcWith<T, H, A>
where
    T: ?Sized + hash::Hash,
    A: Allocator,
{
    #[inline(always)]
    fn hash<HS>(&self, hasher: &mut HS)
    where
        HS: hash::Hasher,
    {
        Self::as_ref(self).hash(hasher);
    }
}

//
//  Ordering
//

impl<T, H, A> Ord for ThinRcWith<T, H, A>
where
    T: ?Sized + Ord,
    A: Allocator,
{
    #[inline(always)]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Self::as_ref(self).cmp(Self::as_ref(other))
    }
}

impl<T, H, A> PartialOrd for ThinRcWith<T, H, A>
where
    T: ?Sized + PartialOrd,
    A: Allocator,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Self::as_ref(self).partial_cmp(Self::as_ref(other))
    }
}

//
//  Markers
//

//  Safety: as Box.
impl<T, H, A> Unpin for ThinRcWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
}

//
//  Reference count.
//

/// Both a strong and a weak reference counts.
#[derive(Debug)]
pub struct ThinRcCount {
    strong: Cell<u64>,
    weak: Cell<u64>,
}

impl ThinRcCount {
    //  Safety:
    //  -   Accounting: should only be invoked when `self.strong` reaches 0.
    #[inline(never)]
    unsafe fn drop<D, DA>(&self, drop: D, deallocate: DA)
    where
        D: FnOnce(),
        DA: FnOnce(),
    {
        struct DropGuard<DA>(ManuallyDrop<DA>)
        where
            DA: FnOnce();

        impl<DA> Drop for DropGuard<DA>
        where
            DA: FnOnce(),
        {
            fn drop(&mut self) {
                //  Safety:
                //  -   EndOfLife: last use.
                let deallocate = unsafe { ManuallyDrop::take(&mut self.0) };

                deallocate();
            }
        }

        let weak = self.weak.get() - 1;

        if weak > 0 {
            self.weak.set(weak);
        }

        let _guard = (weak == 0).then(move || DropGuard(ManuallyDrop::new(deallocate)));

        drop();
    }

    //  Safety:
    //  -   Accounting: should only be invoked when `self.weak` reaches 0.
    #[inline(never)]
    unsafe fn deallocate<DA>(&self, deallocate: DA)
    where
        DA: FnOnce(),
    {
        deallocate();
    }
}

//  Safety:
//  -   Accounting: properly counted.
unsafe impl ThinRefCount for ThinRcCount {
    #[inline(always)]
    fn new() -> Self {
        let strong = Cell::new(1);
        let weak = Cell::new(1);

        Self { strong, weak }
    }

    #[inline(always)]
    fn strong_count(&self) -> u64 {
        self.strong.get()
    }

    #[inline(always)]
    unsafe fn increment_strong(&self) {
        self.strong.update(|c| c + 1);
    }

    #[inline]
    unsafe fn decrement_strong<D, DA>(&self, drop: D, deallocate: DA)
    where
        D: FnOnce(),
        DA: FnOnce(),
    {
        let strong = self.strong.get() - 1;
        self.strong.set(strong);

        if strong > 0 {
            return;
        }

        //  Safety:
        //  -   Accounting: strong count reached 0.
        unsafe { self.drop(drop, deallocate) };
    }
}

//  Safety:
//  -   Accounting: properly counted.
unsafe impl ThinWeakCount for ThinRcCount {
    #[inline(always)]
    fn weak_count(&self) -> u64 {
        self.weak.get()
    }

    #[inline(always)]
    unsafe fn try_increment_strong(&self) -> bool {
        let strong = self.strong.get();

        if strong == 0 {
            return false;
        }

        self.strong.set(strong + 1);

        true
    }

    #[inline(always)]
    unsafe fn increment_weak(&self) {
        self.weak.update(|c| c + 1)
    }

    #[inline]
    unsafe fn decrement_weak<DA>(&self, deallocate: DA)
    where
        DA: FnOnce(),
    {
        let weak = self.weak.get() - 1;

        if weak > 0 {
            self.weak.set(weak);
            return;
        }

        //  Safety:
        //  -   Accounting: weak count reached 0.
        unsafe { self.deallocate(deallocate) };
    }
}

#[cfg(test)]
mod tests {
    use core::{cell::RefCell, fmt::Debug};

    use super::*;

    #[test]
    fn decons_vanilla() {
        let _ = ThinRc::new(value());
    }

    #[test]
    fn decons_with_header() {
        let _ = ThinRcWith::new_with(value(), header());
    }

    #[test]
    fn decons_unsized() {
        let _: ThinRc<dyn Debug> = ThinRc::new_unsize(value());
    }

    #[test]
    fn decons_unsized_with_header() {
        let _: ThinRcWith<dyn Debug, _> = ThinRcWith::new_unsize_with(value(), header());
    }

    #[test]
    fn decons_zst() {
        let _ = ThinRc::new(());
    }

    #[test]
    fn decons_zst_with_header() {
        let _ = ThinRcWith::new_with((), header());
    }

    #[test]
    fn decons_unsized_zst() {
        let _: ThinRc<dyn Debug> = ThinRc::new_unsize(());
    }

    #[test]
    fn decons_unsized_zst_with_header() {
        let _: ThinRcWith<dyn Debug, _> = ThinRcWith::new_unsize_with((), header());
    }

    #[test]
    fn deref_vanilla() {
        let thin = ThinRc::new(value());

        assert_value_mut_str(&thin);
        assert_header_zst(&thin);
    }

    #[test]
    fn deref_with_header() {
        let thin = ThinRcWith::new_with(value(), header());

        assert_value_mut_str(&thin);
        assert_header_mut_boxed(&thin, 33);
    }

    #[test]
    fn deref_zst() {
        let thin = ThinRc::new(());

        assert_value_zst(&thin);
        assert_header_zst(&thin);
    }

    #[test]
    fn deref_zst_with_header() {
        let thin = ThinRcWith::new_with((), header());

        assert_value_zst(&thin);
        assert_header_mut_boxed(&thin, 33);
    }

    #[test]
    fn clone_vanilla() {
        let thin = ThinRc::new(value());
        let clone = ThinRc::clone(&thin);

        {
            let mut t = thin.borrow_mut();
            let s: &mut str = t.as_mut();

            s.make_ascii_lowercase();
        }

        {
            let t = clone.borrow();
            let s: &str = t.as_ref();

            assert_eq!("hello, world!", s);
        }
    }

    #[test]
    fn clone_with_header() {
        const HEADER: u32 = 33;

        let thin = ThinRcWith::new_with(value(), header());
        let clone = ThinRcWith::clone(&thin);

        {
            let header = ThinRcWith::as_header_ref(&thin);
            let mut header = header.borrow_mut();

            **header = HEADER;
        }

        {
            let header = ThinRcWith::as_header_ref(&clone);
            let header = header.borrow();

            assert_eq!(HEADER, **header);
        }
    }

    #[test]
    fn weak_vanilla() {
        let thin = ThinRc::new(value());
        let weak = ThinRc::downgrade(&thin);

        assert_eq!(1, ThinRc::strong_count(&thin));
        assert_eq!(2, ThinRc::weak_count(&thin));

        {
            let mut t = thin.borrow_mut();
            let s: &mut str = t.as_mut();

            s.make_ascii_lowercase();
        }

        assert_eq!(1, ThinRc::strong_count(&thin));
        assert_eq!(2, ThinRc::weak_count(&thin));

        {
            let strong = ThinWeak::upgrade(&weak).expect("still alive");

            assert_eq!(2, ThinRc::strong_count(&strong));

            let t = strong.borrow();
            let s: &str = t.as_ref();

            assert_eq!("hello, world!", s);
        }

        assert_eq!(1, ThinRc::strong_count(&thin));
        assert_eq!(2, ThinRc::weak_count(&thin));

        {
            std::mem::drop(thin);

            assert_eq!(0, ThinWeak::strong_count(&weak));
            assert_eq!(1, ThinWeak::weak_count(&weak));

            let strong = ThinWeak::upgrade(&weak);

            assert!(strong.is_none());
        }
    }

    #[test]
    fn weak_with_header() {
        const HEADER: u32 = 33;

        let thin = ThinRcWith::new_with(value(), header());
        let weak = ThinRcWith::downgrade(&thin);

        assert_eq!(1, ThinRcWith::strong_count(&thin));
        assert_eq!(2, ThinRcWith::weak_count(&thin));

        {
            let header = ThinRcWith::as_header_ref(&thin);
            let mut header = header.borrow_mut();

            **header = HEADER;
        }

        assert_eq!(1, ThinRcWith::strong_count(&thin));
        assert_eq!(2, ThinRcWith::weak_count(&thin));

        {
            let strong = ThinWeakWith::upgrade(&weak).expect("still alive");

            assert_eq!(2, ThinRcWith::strong_count(&strong));

            let header = ThinRcWith::as_header_ref(&strong);
            let header = header.borrow();

            assert_eq!(HEADER, **header);
        }

        assert_eq!(1, ThinRcWith::strong_count(&thin));
        assert_eq!(2, ThinRcWith::weak_count(&thin));

        {
            std::mem::drop(thin);

            assert_eq!(0, ThinWeakWith::strong_count(&weak));
            assert_eq!(1, ThinWeakWith::weak_count(&weak));

            let strong = ThinWeakWith::upgrade(&weak);

            assert!(strong.is_none());
        }
    }

    fn assert_value_mut_str<T, H>(thin: &ThinRcWith<RefCell<T>, H>)
    where
        T: ?Sized + AsMut<str>,
    {
        let t: &RefCell<T> = thin;
        let mut t = t.borrow_mut();
        let s: &mut str = t.as_mut();

        s.make_ascii_lowercase();

        assert_eq!("hello, world!", s);
    }

    fn assert_header_mut_boxed<T, H>(thin: &ThinRcWith<T, RefCell<Box<H>>>, new_header: H)
    where
        T: ?Sized,
        H: Copy + Debug + Eq,
    {
        let header = ThinRcWith::as_header_ref(thin);
        let mut header = header.borrow_mut();

        **header = new_header;

        assert_eq!(new_header, **header);
    }

    fn assert_value_zst<H>(thin: &ThinRcWith<(), H>) {
        assert_eq!((), **thin);
    }

    fn assert_header_zst<T>(thin: &ThinRcWith<T, ()>)
    where
        T: ?Sized,
    {
        let header = ThinRcWith::as_header_ref(thin);

        assert_eq!((), *header);
    }

    //  Why a String?
    //
    //  Using a String is the cheapest way to ensure that the destructor is properly called: Miri will error out with
    //  a memory leak if it is not.
    fn value() -> RefCell<String> {
        RefCell::new(String::from("Hello, World!"))
    }

    //  Why a Box.
    //
    //  Same reason as the String, just a different type.
    fn header() -> RefCell<Box<u32>> {
        RefCell::new(Box::new(42))
    }
} // mod tests
