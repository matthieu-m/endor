//! Thin pointers in various forms.
//!
//! For maximum functionality, the `alloc` feature needs to be activated.
//!
//! #   Available pointers
//!
//! Basic pointers:
//!
//! -   `ThinPtr<T>` and `ThinPtrWith<T, H>`: thin pointers equivalent of `*mut T`, with an optional header `H`.
//! -   `ThinNonNull<T>` and `ThinNonNull<T, H>`: thin pointers equivalent of `NonNull`, with an optional header `H`.
//! -   `ThinAtomicPtr<T>` and `ThinAtomicPtrWith<T, H>`: thin pointers equivalent of `AtomicPtr`, with an optional
//!     header `H`.
//!
//! Allocated pointers:
//!
//! -   `ThinBox<T, A>` and `ThinBoxWith<T, H, A>`: thin pointers equivalent of `Box`, with an optional header `H`.
//! -   `ThinRc<T, A>` and `ThinRcWith<T, H, A>`: thin pointers equivalent of `Rc`, with an optional header `H`.
//! -   `ThinArc<T, A>` and `ThinArcWith<T, H, A>`: thin pointers equivalent of `Arc`, with an optional header `H`.
//!
//! #   Layout
//!
//! A thin pointer memory block layout is composed of two parts:
//!
//! -   The data portion, which contains the actual data, such as `T` if `Sized`.
//! -   The header portion, which contains the header `H`, the pointer metadata, and possibly space for the allocator.
//!
//! The header portion is laid out _in reverse order_, and the thin pointer points not to the start of the memory block
//! but to the `data` portion instead. See this diagram:
//!
//! ```txt
//! +----+-----------+--------+----+---------+------+
//! | .. | allocator | header | .. |metadata | data |
//! +----+-----------+--------+----+---------+------+
//!   ^                         ^            ^
//!   padding                   padding      thin pointer
//! ```

//  Use only core, with `alloc` just a feature away.
#![cfg_attr(not(test), no_std)]
//  Features (language)
#![feature(const_trait_impl)]
//  Features (library)
#![feature(alloc_layout_extra)]
#![feature(allocator_api)]
#![feature(const_option_ops)]
#![feature(phantom_variance_markers)]
#![feature(ptr_metadata)]
#![feature(slice_ptr_get)]
#![cfg_attr(any(test, feature = "alloc"), feature(thin_box))]
#![feature(unsize)]
//  Lints
#![deny(unsafe_op_in_unsafe_fn)]
#![deny(missing_docs)]

//  Non-core must be explicitly depended on in no_std.
#[cfg(feature = "alloc")]
extern crate alloc;

mod atomic;
mod layout;
mod nonnull;
mod ptr;

pub use atomic::{ThinAtomicPtr, ThinAtomicPtrWith};
pub use layout::ThinLayout;
pub use nonnull::{ThinNonNull, ThinNonNullWith};
pub use ptr::{ThinPtr, ThinPtrWith};

#[cfg(feature = "alloc")]
mod arc;

#[cfg(feature = "alloc")]
mod arc_lite;

#[cfg(feature = "alloc")]
mod boxed;

#[cfg(feature = "alloc")]
mod rc;

#[cfg(feature = "alloc")]
mod rc_lite;

#[cfg(feature = "alloc")]
mod raw;

#[cfg(feature = "alloc")]
mod raw_rc;

#[cfg(feature = "alloc")]
pub use arc::{ThinArc, ThinArcCount, ThinArcHeader, ThinArcWith, ThinAwc, ThinAwcWith};

#[cfg(feature = "alloc")]
pub use arc_lite::{ThinArcLite, ThinArcLiteCount, ThinArcLiteHeader, ThinArcLiteWith};

#[cfg(feature = "alloc")]
pub use boxed::{ThinBox, ThinBoxWith};

#[cfg(feature = "alloc")]
pub use rc::{ThinRc, ThinRcCount, ThinRcHeader, ThinRcWith, ThinWeak, ThinWeakWith};

#[cfg(feature = "alloc")]
pub use rc_lite::{ThinRcLite, ThinRcLiteCount, ThinRcLiteHeader, ThinRcLiteWith};

#[cfg(feature = "alloc")]
pub use raw_rc::ThinRefCountHeader;

#[cfg(feature = "alloc")]
pub(crate) use raw::ThinRawWith;

#[cfg(feature = "alloc")]
pub(crate) use raw_rc::{ThinRawRcWith, ThinRawWeakWith, ThinRefCount, ThinWeakCount};
