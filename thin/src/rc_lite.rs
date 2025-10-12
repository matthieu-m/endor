//! Thin pointers equivalent of `Rc<T>`, without weak pointers.
//!
//! For the layout of these thin pointers, refer to the crate-level documentation, noting that there is _always_ a
//! an additional header for the reference count.

use core::{cell::Cell, cmp, convert, fmt, hash, marker::Unsize, mem::ManuallyDrop, ops, pin::Pin, ptr::NonNull};

use alloc::alloc::{AllocError, Allocator, Global};

use crate::{ThinNonNullWith, ThinRawRcWith, ThinRefCount, ThinRefCountHeader};

/// The thin equivalent of `Rc<T, A = Global>`.
pub type ThinRcLite<T, A = Global> = ThinRcLiteWith<T, (), A>;

/// The header used by `ThinRcLiteWith`.
pub type ThinRcLiteHeader<H> = ThinRefCountHeader<H, ThinRcLiteCount>;

/// The thin equivalent of `Rc<T, A = Global>`, with a header of the user's choice.
pub struct ThinRcLiteWith<T, H, A = Global>
where
    T: ?Sized,
    A: Allocator,
{
    inner: ThinRawRcWith<T, H, ThinRcLiteCount, A>,
}

//
//  Conversion
//

impl<T, H, A> ThinRcLiteWith<T, H, A>
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
    pub unsafe fn from_raw(ptr: ThinNonNullWith<T, ThinRcLiteHeader<H>>) -> Self {
        //  Safety:
        //  -   RoundTrip: as per pre-condition.
        let inner = unsafe { ThinRawRcWith::from_non_null(ptr) };

        Self { inner }
    }

    /// Deconstructs the instance, returning a raw pointer instead.
    #[inline(always)]
    pub fn into_non_null(this: Self) -> ThinNonNullWith<T, ThinRcLiteHeader<H>> {
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

//
//  Construction
//

impl<T> ThinRcLiteWith<T, (), Global> {
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

impl<U> ThinRcLiteWith<U, (), Global>
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

impl<T, H> ThinRcLiteWith<T, H, Global> {
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

impl<U, H> ThinRcLiteWith<U, H, Global>
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

impl<T, A> ThinRcLiteWith<T, (), A>
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

impl<U, A> ThinRcLiteWith<U, (), A>
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

impl<T, H, A> ThinRcLiteWith<T, H, A>
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

impl<U, H, A> ThinRcLiteWith<U, H, A>
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

impl<T, H, A> Clone for ThinRcLiteWith<T, H, A>
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

impl<T, H, A> ThinRcLiteWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
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

//
//  Low-level Access
//

impl<T, H, A> ThinRcLiteWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    /// Returns a pointer to the inner data.
    #[inline(always)]
    pub const fn as_non_null(this: &Self) -> ThinNonNullWith<T, ThinRcLiteHeader<H>> {
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

impl<T, H, A> convert::AsRef<T> for ThinRcLiteWith<T, H, A>
where
    T: ?Sized,
    A: Allocator,
{
    fn as_ref(&self) -> &T {
        Self::as_ref(self)
    }
}

impl<T, H, A> ops::Deref for ThinRcLiteWith<T, H, A>
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

impl<T, H, A> fmt::Debug for ThinRcLiteWith<T, H, A>
where
    T: ?Sized + fmt::Debug,
    H: fmt::Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ThinRcLiteWith")
            .field("header", Self::as_header_ref(self))
            .field("value", &Self::as_ref(self))
            .finish()
    }
}

impl<T, H, A> fmt::Display for ThinRcLiteWith<T, H, A>
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

impl<T, H, A> Eq for ThinRcLiteWith<T, H, A>
where
    T: ?Sized + Eq,
    A: Allocator,
{
}

impl<T, H, A> PartialEq for ThinRcLiteWith<T, H, A>
where
    T: ?Sized + PartialEq,
    A: Allocator,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        Self::as_ref(self).eq(Self::as_ref(other))
    }
}

impl<T, H, A> hash::Hash for ThinRcLiteWith<T, H, A>
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

impl<T, H, A> Ord for ThinRcLiteWith<T, H, A>
where
    T: ?Sized + Ord,
    A: Allocator,
{
    #[inline(always)]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Self::as_ref(self).cmp(Self::as_ref(other))
    }
}

impl<T, H, A> PartialOrd for ThinRcLiteWith<T, H, A>
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
impl<T, H, A> Unpin for ThinRcLiteWith<T, H, A>
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
pub struct ThinRcLiteCount {
    strong: Cell<u64>,
}

impl ThinRcLiteCount {
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

        let _guard = DropGuard(ManuallyDrop::new(deallocate));

        drop();
    }
}

//  Safety:
//  -   Accounting: properly counted.
unsafe impl ThinRefCount for ThinRcLiteCount {
    #[inline(always)]
    fn new() -> Self {
        let strong = Cell::new(1);

        Self { strong }
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

        if strong > 0 {
            self.strong.set(strong);
            return;
        }

        //  Safety:
        //  -   Accounting: strong count reached 0.
        unsafe { self.drop(drop, deallocate) };
    }
}

#[cfg(test)]
mod tests {
    use core::{cell::RefCell, fmt::Debug};

    use super::*;

    #[test]
    fn decons_vanilla() {
        let _ = ThinRcLite::new(value());
    }

    #[test]
    fn decons_with_header() {
        let _ = ThinRcLiteWith::new_with(value(), header());
    }

    #[test]
    fn decons_unsized() {
        let _: ThinRcLite<dyn Debug> = ThinRcLite::new_unsize(value());
    }

    #[test]
    fn decons_unsized_with_header() {
        let _: ThinRcLiteWith<dyn Debug, _> = ThinRcLiteWith::new_unsize_with(value(), header());
    }

    #[test]
    fn decons_zst() {
        let _ = ThinRcLite::new(());
    }

    #[test]
    fn decons_zst_with_header() {
        let _ = ThinRcLiteWith::new_with((), header());
    }

    #[test]
    fn decons_unsized_zst() {
        let _: ThinRcLite<dyn Debug> = ThinRcLite::new_unsize(());
    }

    #[test]
    fn decons_unsized_zst_with_header() {
        let _: ThinRcLiteWith<dyn Debug, _> = ThinRcLiteWith::new_unsize_with((), header());
    }

    #[test]
    fn deref_vanilla() {
        let thin = ThinRcLite::new(value());

        assert_value_mut_str(&thin);
        assert_header_zst(&thin);
    }

    #[test]
    fn deref_with_header() {
        let thin = ThinRcLiteWith::new_with(value(), header());

        assert_value_mut_str(&thin);
        assert_header_mut_boxed(&thin, 33);
    }

    #[test]
    fn deref_zst() {
        let thin = ThinRcLite::new(());

        assert_value_zst(&thin);
        assert_header_zst(&thin);
    }

    #[test]
    fn deref_zst_with_header() {
        let thin = ThinRcLiteWith::new_with((), header());

        assert_value_zst(&thin);
        assert_header_mut_boxed(&thin, 33);
    }

    #[test]
    fn clone_vanilla() {
        let thin = ThinRcLite::new(value());
        let clone = ThinRcLite::clone(&thin);

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

        let thin = ThinRcLiteWith::new_with(value(), header());
        let clone = ThinRcLiteWith::clone(&thin);

        {
            let header = ThinRcLiteWith::as_header_ref(&thin);
            let mut header = header.borrow_mut();

            **header = HEADER;
        }

        {
            let header = ThinRcLiteWith::as_header_ref(&clone);
            let header = header.borrow();

            assert_eq!(HEADER, **header);
        }
    }

    fn assert_value_mut_str<T, H>(thin: &ThinRcLiteWith<RefCell<T>, H>)
    where
        T: ?Sized + AsMut<str>,
    {
        let t: &RefCell<T> = thin;
        let mut t = t.borrow_mut();
        let s: &mut str = t.as_mut();

        s.make_ascii_lowercase();

        assert_eq!("hello, world!", s);
    }

    fn assert_header_mut_boxed<T, H>(thin: &ThinRcLiteWith<T, RefCell<Box<H>>>, new_header: H)
    where
        T: ?Sized,
        H: Copy + Debug + Eq,
    {
        let header = ThinRcLiteWith::as_header_ref(thin);
        let mut header = header.borrow_mut();

        **header = new_header;

        assert_eq!(new_header, **header);
    }

    fn assert_value_zst<H>(thin: &ThinRcLiteWith<(), H>) {
        assert_eq!((), **thin);
    }

    fn assert_header_zst<T>(thin: &ThinRcLiteWith<T, ()>)
    where
        T: ?Sized,
    {
        let header = ThinRcLiteWith::as_header_ref(thin);

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
