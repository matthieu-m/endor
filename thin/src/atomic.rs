//! Thin pointer equivalent of `AtomicPtr<T>`.

use core::{
    fmt,
    marker::PhantomInvariant,
    panic,
    sync::atomic::{AtomicPtr, Ordering},
};

use crate::ThinPtrWith;

/// Thin pointer equivalent of `AtomicPtr<T>`.
pub type ThinAtomicPtr<T> = ThinAtomicPtrWith<T, ()>;

/// Thin pointer equivalent of `AtomicPtr<T>`, with a header `H`.
pub struct ThinAtomicPtrWith<T, H>
where
    T: ?Sized,
{
    ptr: AtomicPtr<u8>,
    _data: PhantomInvariant<T>,
    _header: PhantomInvariant<H>,
}

//
//  Construction
//

impl<T, H> ThinAtomicPtrWith<T, H>
where
    T: ?Sized,
{
    /// Constructs a new instance.
    #[inline(always)]
    pub const fn new(ptr: ThinPtrWith<T, H>) -> Self {
        let ptr = AtomicPtr::new(ptr.into_raw());
        let _data = PhantomInvariant::new();
        let _header = PhantomInvariant::new();

        Self { ptr, _data, _header }
    }
}

impl<T> Default for ThinAtomicPtrWith<T, ()> {
    fn default() -> Self {
        Self::new(ThinPtrWith::null())
    }
}

//
//  Destruction
//

impl<T, H> ThinAtomicPtrWith<T, H>
where
    T: ?Sized,
{
    /// Returns the inner pointer.
    #[inline(always)]
    pub const fn into_inner(self) -> ThinPtrWith<T, H> {
        ThinPtrWith::from_raw(self.ptr.into_inner())
    }
}

//
//  Access
//

impl<T, H> ThinAtomicPtrWith<T, H>
where
    T: ?Sized,
{
    /// Loads the value.
    #[inline(always)]
    pub fn load(&self, order: Ordering) -> ThinPtrWith<T, H> {
        ThinPtrWith::from_raw(self.ptr.load(order))
    }

    /// Stores a new value.
    #[inline(always)]
    pub fn store(&self, ptr: ThinPtrWith<T, H>, order: Ordering) {
        self.ptr.store(ptr.into_raw(), order)
    }

    /// Swaps the value a new value.
    #[inline(always)]
    pub fn swap(&self, ptr: ThinPtrWith<T, H>, order: Ordering) -> ThinPtrWith<T, H> {
        ThinPtrWith::from_raw(self.ptr.swap(ptr.into_raw(), order))
    }

    /// Stores `new` in `self` if the current value is `current`.
    ///
    /// See `AtomicPtr::compare_exchange` for more information.
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        current: ThinPtrWith<T, H>,
        new: ThinPtrWith<T, H>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<ThinPtrWith<T, H>, ThinPtrWith<T, H>> {
        self.ptr
            .compare_exchange(current.into_raw(), new.into_raw(), success, failure)
            .map(ThinPtrWith::from_raw)
            .map_err(ThinPtrWith::from_raw)
    }

    /// Stores `new` in `self` if the current value is `current`.
    ///
    /// See `AtomicPtr::compare_exchange_weak` for more information.
    #[inline(always)]
    pub fn compare_exchange_weak(
        &self,
        current: ThinPtrWith<T, H>,
        new: ThinPtrWith<T, H>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<ThinPtrWith<T, H>, ThinPtrWith<T, H>> {
        self.ptr
            .compare_exchange_weak(current.into_raw(), new.into_raw(), success, failure)
            .map(ThinPtrWith::from_raw)
            .map_err(ThinPtrWith::from_raw)
    }

    /// Stores `new` in `self` if the current value is `current`.
    ///
    /// See `AtomicPtr::fetch_update` for more information.
    #[inline(always)]
    pub fn fetch_update<F>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        f: F,
    ) -> Result<ThinPtrWith<T, H>, ThinPtrWith<T, H>>
    where
        F: FnMut(ThinPtrWith<T, H>) -> Option<ThinPtrWith<T, H>>,
    {
        let mut f = f;
        let f = move |ptr| f(ThinPtrWith::from_raw(ptr)).map(ThinPtrWith::into_raw);

        self.ptr
            .fetch_update(set_order, fetch_order, f)
            .map(ThinPtrWith::from_raw)
            .map_err(ThinPtrWith::from_raw)
    }
}

//
//  Traits
//

impl<T, H> fmt::Debug for ThinAtomicPtrWith<T, H>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Debug::fmt(&self.load(Ordering::Relaxed), f)
    }
}

impl<T, H> fmt::Pointer for ThinAtomicPtrWith<T, H>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Pointer::fmt(&self.load(Ordering::Relaxed), f)
    }
}

impl<T, H> From<ThinPtrWith<T, H>> for ThinAtomicPtrWith<T, H>
where
    T: ?Sized,
{
    fn from(ptr: ThinPtrWith<T, H>) -> Self {
        Self::new(ptr)
    }
}

impl<T, H> panic::RefUnwindSafe for ThinAtomicPtrWith<T, H> where T: ?Sized {}

//  Safety: as per AtomicPtr<T>.
unsafe impl<T, H> Send for ThinAtomicPtrWith<T, H> where T: ?Sized {}
unsafe impl<T, H> Sync for ThinAtomicPtrWith<T, H> where T: ?Sized {}
