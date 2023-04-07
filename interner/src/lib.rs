//! Quasi wait-free string interner.
//!
//! The `Interner` is a quasi wait-free data-structure to intern strings, and is specifically designed to be used
//! from many threads in parallel.
//!
//!
//! #   How to use?
//!
//! If you just want to get going, use the `new` method, and you'll get a default configured `Interner` which
//! will be quite fine.
//!
//! You can always tune it later, using the configuration options.
//!
//!
//! #   Configuration options
//!
//! The `Interner` offers multiple configuration options, available via the `InternerBuilder`:
//!
//! -   The hashing algorithm can be tuned, it defaults to Fx Hash.
//! -   The number of shards can be tuned, it defaults to 16. It is recommended to use about twice the number of
//!     logical cores, up to a maximum of 256.
//! -   The initial amount of memory used by a shard can be tuned, both for its string storage area and its hashtable
//!     area.
//!
//!
//! #   Limits
//!
//! The `Interner` has some hard limits, due to design constraints:
//!
//! -   It supports only up to 256 shards, eg. 2**8.
//! -   It supports only strings up to 4GB, eg. 2**32.
//! -   It supports only up to 4 billions unique strings, eg. 2**32.
//!
//!
//! #   Internals
//!
//! The `Interner` is a sharded data-structure:
//!
//! -   When inserting a `[u8]`, 8 bits off the hash are used to determine which shard to use, then are embedded in the
//!     `BytesId` returned.
//! -   When looking-up a `[u8]` by `BytesId`, the 8 bits are extracted from it and used to determine which shard to
//!     look into.
//!
//! The array of shards is pre-allocated, though each shard starts off empty. Each shard operates in complete isolation
//! so that sharding is the primary mean to avoid contention.
//!
//! Each shard contains two distinct areas:
//!
//! -   A byte store, in which all strings are catenated. On top of its 8 bits shard ID, the `BytesId` contains a
//!     32-bits offset within the byte store. The length is stored in the 4 bytes preceeding the memory pointed to by
//!     the offset.
//! -   A hashmap, referencing slices of the byte store.
//!
//! Both the byte store and hashmap are "jagged", growing by adding more dynamically allocated arrays, and never
//! freeing (nor ceasing to use) the existing arrays. This is the key to wait-freedom.
//!
//! Each array within the byte store contains its own "used" counter, and is used bump-allocator style. Inserting into
//! the byte store is wait-free if there's enough memory, or if allocating is wait-free.
//!
//! The hashmaps, instead, use a Swiss Map design, which is mostly wait-free, with the one exception being
//! concurrently inserting two slices with a colliding hash residual within the same shard, as the second must wait for
//! the insertion of the first to check for equality.

//  Use only core and alloc, guaranteeing no I/O nor threads.
#![cfg_attr(not(test), no_std)]
//  Collections should use flexible allocators.
#![feature(allocator_api)]
//  Error is very useful...
#![feature(error_in_core)]
//  `NonNull` is unfortunately locked away :(
#![feature(slice_ptr_get)]
//  Ensure unsafe operations are duly checked.
#![deny(unsafe_op_in_unsafe_fn)]
//  Ensure proper documentation.
#![deny(missing_docs)]

//  Non-core must be explicitly depended on in no_std.
extern crate alloc;

mod error;
mod hash;
mod id;
mod interner;
mod shard;

pub use error::InternerError;
pub use hash::{DefaultFxBuildHasher, FxBuildHasher, FxHasher};
pub use id::{BytesId, Id, StringId};
pub use interner::{Interner, InternerBuilder};
