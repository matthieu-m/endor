//  A single shard of the interner, completely independent from the others.

use core::{
    alloc::Layout,
    cmp, fmt, hint, mem,
    num::NonZeroU32,
    ptr::{self, NonNull},
    sync::atomic::{AtomicPtr, AtomicU32, AtomicU64, AtomicU8, Ordering},
};

use alloc::alloc::Allocator;

use crate::{
    error::InternerError,
    id::{Offset, ShardIndex},
};

/// Common fields of all shards.
pub(crate) struct ShardDirector<A> {
    log_number_shards: u8,
    log_initial_bytes: u8,
    log_initial_groups: u8,
    allocator: A,
}

impl<A> ShardDirector<A> {
    /// Creates a new director.
    pub(crate) fn new(log_number_shards: u8, log_initial_bytes: u8, log_initial_groups: u8, allocator: A) -> Self {
        Self {
            log_number_shards,
            log_initial_bytes,
            log_initial_groups,
            allocator,
        }
    }

    /// Splits a hash into shard index / residual / hash.
    #[inline(always)]
    pub(crate) fn split_hash(&self, hash: u64) -> (ShardIndex, u8, u64) {
        debug_assert!(self.log_number_shards <= 8);

        let shard_mask = (1u64 << self.log_number_shards) - 1;

        let shard = (hash & shard_mask) as u8;
        let residual = (hash >> 8) as u8 & 0x7F;
        let hash = hash >> 15;

        let residual = cmp::max(residual, 1);

        (ShardIndex(shard), residual, hash)
    }

    /// Returns the number of shards.
    pub(crate) fn number_shards(&self) -> usize {
        1usize << self.log_number_shards
    }

    /// Returns a reference to the allocator.
    pub(crate) fn allocator(&self) -> &A {
        &self.allocator
    }
}

impl<A> fmt::Debug for ShardDirector<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ShardDirector")
            .field("log_number_shards", &self.log_number_shards)
            .field("log_initial_bytes", &self.log_initial_bytes)
            .field("log_initial_groups", &self.log_initial_groups)
            .finish()
    }
}

/// A single shard, combining jagged byte store and jagged swiss map.
pub(crate) struct Shard {
    store: Store,
    map: Map,
}

impl Shard {
    /// Drops any acquired resource, returning the instance to an empty, blank, state.
    ///
    /// #   Safety
    ///
    /// This `director` must have been used for all insertions in this instance.
    pub(crate) unsafe fn reset<A>(&mut self, director: &ShardDirector<A>)
    where
        A: Allocator,
    {
        //  Safety:
        //  -   The same `allocator` instance was used for all operations.
        unsafe {
            self.store.reset(director);
            self.map.reset(director);
        }
    }

    /// Attempts to get a slice.
    ///
    /// No bounds check is performed, and shared access to the underlying slice is assumed.
    ///
    /// #   Safety
    ///
    /// -   `offset` must have been obtained from this instance.
    /// -   This instance must not have been reset since `offset` was obtained.
    /// -   This `director` must have been used for all previous insertions in this instance.
    ///
    /// #   Complexity
    ///
    /// O(1) in time and space.
    pub(crate) unsafe fn get_unchecked<'a, A>(&'a self, offset: Offset, director: &ShardDirector<A>) -> &'a [u8] {
        //  Safety:
        //  -   `id` was obtained from this instance.
        //  -   This instance has not been reset since `id` was obtained.
        unsafe { self.store.get_slice_unchecked(offset, director) }
    }

    /// Attempts to insert a slice, returning its offset and length.
    ///
    /// Insertion may only fail if there is no room to insert it, which may be the result of various conditions:
    ///
    /// -   There may not be any more room to insert bytes in the bytes store.
    /// -   There may not be any more room to insert a reference in the map.
    /// -   There may have been too many collisions for this particular hash value, leading to a full bucket.
    /// -   The allocator may not be able to allocate memory.
    ///
    /// #   Safety
    ///
    /// This `director` must have been used for all previous insertions in this instance.
    ///
    /// #   Complexity
    ///
    /// -   O(slice.len()) due to copying the slice.
    /// -   O(number-parts) due to attempting to fit the slice in all parts in the worse case.
    pub(crate) unsafe fn insert<A>(
        &self,
        hash: u64,
        slice: &[u8],
        director: &ShardDirector<A>,
    ) -> Result<Offset, InternerError>
    where
        A: Allocator,
    {
        //  Safety:
        //  -   This `director` has been used for all previous insertions in `self.map`.
        unsafe { self.map.insert(hash, slice, &self.store, director) }
    }

    /// Iterator over the slices stored, with their metadata.
    ///
    /// Note that it is unknown (to `self`) whether the slice of bytes is actually a string, or not.
    ///
    /// #   Safety
    ///
    /// This `director` must have been used for all insertions in this instance.
    pub(crate) unsafe fn iter_with_metadata<'a, A>(
        &'a self,
        director: &'a ShardDirector<A>,
    ) -> impl Iterator<Item = (&'a [u8], StoreMetadata, MapMetadata)> + 'a {
        //  Safety:
        //  -   The `director` has been used for all insertions in this instance.
        let offset_with_metadata = unsafe { self.map.iter_with_metadata(director) };

        offset_with_metadata.map(|(offset, map)| {
            //  Safety:
            //  -   `offset` was obtained from this instance.
            //  -   This instance has not been reset since `offset` was obtained.
            //  -   This `director` has been used for all previous insertions in this instance.
            let (slice, store) = unsafe { self.store.get_slice_unchecked_with_metadata(offset, director) };

            (slice, store, map)
        })
    }
}

/// Metadata (exact location) of the slice within the bytes store.
pub(crate) struct StoreMetadata {
    /// Index of the part in which the slice is located.
    pub(crate) part: usize,
    /// Offset of the slice within the part.
    pub(crate) offset: usize,
}

/// Metadata (exact location) of the slice's Offset within the map.
pub(crate) struct MapMetadata {
    /// Index of the part in which the offset is located.
    pub(crate) part: usize,
    /// Index of the group within the part in which the offset is located.
    pub(crate) group: usize,
    /// Index of the element within the group in which the offset is located.
    pub(crate) index: usize,
}

//
//  Implementation
//

const GROUP_LENGTH: usize = 16;
const JAGGED_LENGTH: usize = 16;
const PROBING_SEQUENCE: [u64; 4] = [0, 1, 3, 7];
const SLICE_LENGTH_BYTES: u64 = mem::size_of::<SliceLength>() as u64;

type SliceLength = u32;

type PartLength = AtomicU64;

//  Index of a part of a jagged container.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct PartIndex(usize);

//  Index of the bytes within a part of the bytes storage.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ByteIndex(usize);

impl<A> ShardDirector<A> {
    //  Returns the number of bytes of the part at the given index.
    fn bytes_of(&self, index: PartIndex) -> usize {
        if index.0 == 0 {
            1usize << self.log_initial_bytes
        } else {
            (1usize << self.log_initial_bytes) << (index.0 - 1)
        }
    }

    //  Returns the number of bytes _prior_ to the part at the given index.
    fn previous_bytes_of(&self, index: PartIndex) -> usize {
        if index.0 > 0 {
            self.bytes_of(index)
        } else {
            0
        }
    }

    //  Returns the index of the part, and within the part, of the given offset.
    fn bytes_part_of(&self, offset: Offset) -> (PartIndex, ByteIndex) {
        let offset = offset.0.get() as usize;

        let outer = {
            let outer = offset >> self.log_initial_bytes;

            mem::size_of::<usize>() * 8 - outer.leading_zeros() as usize
        };

        debug_assert!(self.previous_bytes_of(PartIndex(outer)) <= offset);
        debug_assert!(offset < self.bytes_of(PartIndex(outer + 1)));

        (
            PartIndex(outer),
            ByteIndex(offset - self.previous_bytes_of(PartIndex(outer))),
        )
    }

    fn groups_of(&self, index: PartIndex) -> usize {
        if index.0 == 0 {
            1usize << self.log_initial_groups
        } else {
            (1usize << self.log_initial_groups) << (index.0 - 1)
        }
    }

    fn layout_bytes(&self, index: PartIndex) -> Option<Layout> {
        let number_bytes = self.bytes_of(index);

        Layout::from_size_align(number_bytes, 1).ok()
    }

    fn layout_groups(&self, index: PartIndex) -> Option<Layout> {
        Layout::array::<MapGroup>(self.groups_of(index)).ok()
    }
}

impl<A> ShardDirector<A>
where
    A: Allocator,
{
    fn allocate_bytes(&self, index: PartIndex) -> Result<NonNull<u8>, InternerError> {
        let Some(layout) = self.layout_bytes(index) else {
            return Err(InternerError::MemoryExhausted);
        };

        self.allocator
            .allocate_zeroed(layout)
            .map(|n| n.as_non_null_ptr())
            .map_err(|_| InternerError::MemoryExhausted)
    }

    fn allocate_groups(&self, index: PartIndex) -> Result<NonNull<MapGroup>, InternerError> {
        let Some(layout) = self.layout_groups(index) else {
            return Err(InternerError::MemoryExhausted);
        };

        self.allocator
            .allocate_zeroed(layout)
            .map(|n| n.as_non_null_ptr().cast())
            .map_err(|_| InternerError::MemoryExhausted)
    }

    //  #   Safety:
    //
    //  -   `ptr` must have been allocated by this instance's `allocate_bytes`, and not have been deallocated.
    //  -   `ptr` must have been allocated with this `index`.
    unsafe fn deallocate_bytes(&self, ptr: NonNull<u8>, index: PartIndex) {
        let layout = self
            .layout_bytes(index)
            .expect("Not to overflow, since it was allocated...");

        //  Safety:
        //  -   `ptr` denotes a block of memory currently allocated by this allocator.
        //  -   `ptr` was allocated with this `layout`.
        unsafe { self.allocator.deallocate(ptr, layout) }
    }

    //  #   Safety
    //
    //  -   `ptr` must have been allocated by this instance's `allocate_groups`, and not have been deallocated.
    //  -   `ptr` must have been allocated with this `index`.
    unsafe fn deallocate_groups(&self, ptr: NonNull<MapGroup>, index: PartIndex) {
        let layout = self
            .layout_groups(index)
            .expect("Not to overflow, since it was allocated...");

        //  Safety:
        //  -   `ptr` denotes a block of memory currently allocated by this allocator.
        //  -   `ptr` was allocated with this `layout`.
        unsafe { self.allocator.deallocate(ptr.cast(), layout) };
    }
}

#[derive(Default)]
struct Store {
    //  It is tempting to prepend the length in the memory allocation pointed to by part, however this is undesirable
    //  for two reasons:
    //
    //  1.  Memory indirection - it makes it impossible to read the length without having first dereferenced `parts[i]`.
    //  2.  Allocation size - memory allocators are friands of power-of-2 sized allocations, adding a measly 8 bytes on
    //      top requires the allocator to use the next allocation size, wasting quite a bit. While not a problem
    //      cache-wise, it may still be a problem for custom allocators with limited available memory.
    lengths: [PartLength; JAGGED_LENGTH],
    parts: [AtomicPtr<u8>; JAGGED_LENGTH],
}

impl Store {
    //  Resets the store, invalidating all allocated `Offset`.
    //
    //  #   Safety
    //
    //  This `director` must have been used for all previous insertions in this instance.
    unsafe fn reset<A>(&mut self, director: &ShardDirector<A>)
    where
        A: Allocator,
    {
        for (part, (length, pointer)) in self.lengths.iter().zip(self.parts.iter()).enumerate() {
            let part = PartIndex(part);

            length.store(0, Ordering::Relaxed);

            let pointer = pointer.swap(ptr::null_mut(), Ordering::Relaxed);

            let Some(pointer) = NonNull::new(pointer) else { continue };

            //  Safety:
            //  -   `pointer` is currently allocated by this allocator.
            //  -   `pointer` was allocated with this `part`.
            unsafe { director.deallocate_bytes(pointer, part) };
        }
    }

    //  Returns the matching slice.
    //
    //  #   Safety
    //
    //  -   `offset` must have been obtained from this instance.
    //  -   This instance must not have been reset since `offset` was obtained.
    //  -   This `director` must have been used for all previous insertions in this instance.
    //
    //  #   Complexity
    //
    //  O(1) in time and space.
    unsafe fn get_slice_unchecked<'a, A>(&'a self, offset: Offset, director: &ShardDirector<A>) -> &'a [u8] {
        //  Safety:
        //  -   `offset` was obtained from this instance.
        //  -   This instance has not been reset since `offset` was obtained.
        //  -   This `director` has been used for all previous insertions in this instance.
        let (result, _) = unsafe { self.get_slice_unchecked_with_metadata(offset, director) };

        result
    }

    //  Returns the matching slice.
    //
    //  #   Safety
    //
    //  -   `offset` must have been obtained from this instance.
    //  -   This instance must not have been reset since `offset` was obtained.
    //  -   This `director` must have been used for all previous insertions in this instance.
    //
    //  #   Complexity
    //
    //  O(1) in time and space.
    unsafe fn get_slice_unchecked_with_metadata<'a, A>(
        &'a self,
        offset: Offset,
        director: &ShardDirector<A>,
    ) -> (&'a [u8], StoreMetadata) {
        let (part, inner) = director.bytes_part_of(offset);

        let metadata = StoreMetadata {
            part: part.0,
            offset: inner.0,
        };

        debug_assert!(part.0 < self.parts.len(), "{} < {}", part.0, self.parts.len());

        //  Safety:
        //  -   `part` is within bounds, since `offset` exists.
        let pointer = unsafe { self.parts.get_unchecked(part.0) };

        let pointer = pointer.load(Ordering::Relaxed);

        debug_assert!(
            inner.0 < director.bytes_of(part),
            "{} < {}",
            inner.0,
            director.bytes_of(part)
        );
        debug_assert!(
            (inner.0 as u64) <= self.lengths[part.0].load(Ordering::Relaxed),
            "{} <= {}",
            inner.0,
            self.lengths[part.0].load(Ordering::Relaxed)
        );

        //  Safety:
        //  -   `inner` is guaranteed to be within the allocation, or one past its end.
        let pointer = unsafe { pointer.add(inner.0) };

        debug_assert!(inner.0 >= mem::size_of::<SliceLength>());

        //  Safety:
        //  -   The length is recorded prior to any bytes.
        let length_pointer = unsafe { pointer.sub(mem::size_of::<SliceLength>()) };

        //  Safety:
        //  -   `length_pointer` is valid for reads.
        //  -   `length_pointer` points to an initialized instance.
        let length = unsafe { ptr::read_unaligned(length_pointer as *const SliceLength) };

        //  Safety:
        //  -   `pointer` is valid for read of `length` bytes.
        //  -   `pointer` points to `length` initialized bytes.
        //  -   The memory referenced by the slice will not be mutated during its lifetime since the store is
        //      append-only.
        //  -   `length` is not larger than `isize::MAX`, since the allocation succeeded.
        let slice = unsafe { core::slice::from_raw_parts(pointer, length as usize) };

        (slice, metadata)
    }

    //  Pushes the slice, returning the offset and length, or None if it could not be inserted.
    //
    //  #   Safety
    //
    //  This `director` must have been used for all previous insertions in this instance.
    //
    //  #   Complexity
    //
    //  -   O(slice.len()) due to copying the slice.
    //  -   O(self.0.len()) due to attempting to fit the slice in all parts in the worse case.
    unsafe fn push_slice<A>(&self, slice: &[u8], director: &ShardDirector<A>) -> Result<Offset, InternerError>
    where
        A: Allocator,
    {
        debug_assert!(slice.len() <= SliceLength::MAX as usize);

        for (part, (part_length, pointer)) in self.lengths.iter().zip(self.parts.iter()).enumerate() {
            let part = PartIndex(part);

            let bytes = pointer.load(Ordering::Relaxed);

            let bytes = if let Some(bytes) = NonNull::new(bytes) {
                bytes
            } else {
                Self::try_allocate(part, pointer, director)?
            };

            let previous_offset = if part.0 > 0 {
                director
                    .previous_bytes_of(part)
                    .try_into()
                    .map_err(|_| InternerError::ByteStorageExhausted)?
            } else {
                0
            };

            let length = director.bytes_of(part);

            let part = NonNull::slice_from_raw_parts(bytes, length);

            //  Safety:
            //  -   `part_length` matches `part`.
            let offset = unsafe { Self::push_slice_in_part(previous_offset, part_length, part, slice) };

            match offset {
                Err(InternerError::ByteStorageExhausted) => continue,
                offset => return offset,
            }
        }

        Err(InternerError::ByteStorageExhausted)
    }

    //  Pushes the slice, returning the offset and length, or None if it could not be inserted.
    //
    //  #   Safety
    //
    //  - `part_length` must match `part`.
    unsafe fn push_slice_in_part(
        previous_offset: u32,
        part_length: &PartLength,
        part: NonNull<[u8]>,
        slice: &[u8],
    ) -> Result<Offset, InternerError> {
        let length = slice.len() as u64;
        let number_bytes = part.len() as u64;

        //  Quick check to avoid incrementing pointlessly:
        //
        //  -   It's good safety wise, to avoid overflow.
        //  -   It's good performance wise, as pure reads are cheaper than RMV.
        if part_length.load(Ordering::Relaxed) + length + SLICE_LENGTH_BYTES > number_bytes {
            return Err(InternerError::ByteStorageExhausted);
        }

        //  Of course, with concurrency, there may still be other threads adding before we do.
        let previous_part_length = part_length.fetch_add(length + SLICE_LENGTH_BYTES, Ordering::Relaxed);

        //  If the offset cannot be encoded, no point going any further...
        let offset = || -> Option<NonZeroU32> {
            let inner_offset: u32 = (previous_part_length + SLICE_LENGTH_BYTES).try_into().ok()?;

            let offset = previous_offset.checked_add(inner_offset)?;

            NonZeroU32::new(offset)
        };

        let Some(offset) = offset() else {
            return Err(InternerError::ByteStorageExhausted);
        };

        //  Got beaten to the punch, bail out and let the outer loop move on to the next part.
        if previous_part_length + length + SLICE_LENGTH_BYTES > number_bytes {
            return Err(InternerError::ByteStorageExhausted);
        }

        //  Exclusive access to `previous_part_length..(+length+SLICE_LENGTH_BYTES)` has been secured!

        //  Safety:
        //  -   Within bounds of the allocation, thus will not overflow.
        let length_pointer = unsafe { part.as_mut_ptr().add(previous_part_length as usize) };

        //  Safety:
        //  -   `length_pointer` is valid for writes.
        unsafe { ptr::write_unaligned(length_pointer as *mut SliceLength, slice.len() as SliceLength) };

        //  Safety:
        //  -   Within bounds of the allocation, thus will not overflow.
        let pointer = unsafe { length_pointer.add(SLICE_LENGTH_BYTES as usize) };

        //  Safety:
        //  -   `pointer` is valid for both reads and writes of `slice.len()` bytes.
        //  -   `pointer` points to `slice.len()` initialized bytes.
        //  -   The memory referenced by the slice is exclusively reserved for the lifetime of `destination`.
        //  -   The total size of the slice is no larger than `isize::MAX`, since it's already a slice length.
        let destination = unsafe { core::slice::from_raw_parts_mut(pointer, slice.len()) };

        destination.copy_from_slice(slice);

        Ok(Offset(offset))
    }

    //  Tries to allocate a new part at `index`.
    //
    //  Failure means that another thread allocated, so that when `try_allocate` returns, the part at `index` is ready.
    fn try_allocate<A>(
        part: PartIndex,
        pointer: &AtomicPtr<u8>,
        director: &ShardDirector<A>,
    ) -> Result<NonNull<u8>, InternerError>
    where
        A: Allocator,
    {
        let mut bytes = director.allocate_bytes(part)?;

        let current = ptr::null_mut();

        if let Err(p) = pointer.compare_exchange(current, bytes.as_ptr(), Ordering::Relaxed, Ordering::Relaxed) {
            //  Safety:
            //  -   Freshly allocated.
            unsafe { director.deallocate_bytes(bytes, part) };

            //  Safety:
            //  -   Non-null, or `compare_exchange` would have succeeded.
            bytes = unsafe { NonNull::new_unchecked(p) }
        }

        Ok(bytes)
    }
}

//  Safety:
//  -   A store is safe to send across threads, and safe to access concurrently from multiple threads.
unsafe impl Send for Store {}
unsafe impl Sync for Store {}

#[derive(Default)]
struct Map([AtomicPtr<MapGroup>; JAGGED_LENGTH]);

//  Ensure the header is aligned on 16-bytes boundary, for SIMD instructions.
#[derive(Default)]
#[repr(C, align(16))]
struct MapGroup {
    header: [AtomicU8; GROUP_LENGTH],
    elements: [AtomicU32; GROUP_LENGTH],
}

impl Map {
    //  Resets the map, invalidating all allocated `Offset`.
    //
    //  #   Safety
    //
    //  This `director` must have been used for all previous insertions in this instance.
    unsafe fn reset<A>(&self, director: &ShardDirector<A>)
    where
        A: Allocator,
    {
        for (part, pointer) in self.0.iter().enumerate() {
            let part = PartIndex(part);

            let pointer = pointer.swap(ptr::null_mut(), Ordering::Relaxed);
            let Some(pointer) = NonNull::new(pointer) else { continue };

            //  Safety:
            //  -   `pointer` is currently allocated by this allocator.
            //  -   `pointer` was allocated with this `part`.
            unsafe { director.deallocate_groups(pointer, part) };
        }
    }

    //  Returns an iterator over known offsets, tagged with the exact location of each offset.
    //
    //  #   Safety
    //
    //  This `director` must have been used for all previous insertions in this instance.
    unsafe fn iter_with_metadata<'a, A>(
        &'a self,
        director: &'a ShardDirector<A>,
    ) -> impl Iterator<Item = (Offset, MapMetadata)> + 'a {
        self.0.iter().enumerate().flat_map(|(part_index, part)| {
            let part = part.load(Ordering::Relaxed);
            let part_index = PartIndex(part_index);

            let number_groups = if part.is_null() {
                0
            } else {
                director.groups_of(part_index)
            };

            //  Safety:
            //  -   `number_groups` is the number of groups pointed to by the part pointer.
            let groups = unsafe { core::slice::from_raw_parts(part, number_groups) };

            groups.iter().enumerate().flat_map(move |(group_index, group)| {
                group
                    .header
                    .iter()
                    .zip(group.elements.iter())
                    .enumerate()
                    .filter_map(move |(index, (h, e))| {
                        let residual = h.load(Ordering::Acquire);
                        let metadata = MapMetadata {
                            part: part_index.0,
                            group: group_index,
                            index,
                        };

                        if residual > 0 && residual < 0x80 {
                            let offset = e.load(Ordering::Relaxed);

                            //  Safety:
                            //  -   `offset` is non-zero, as only non-zero are stored.
                            let offset = unsafe { NonZeroU32::new_unchecked(offset) };

                            Some((Offset(offset), metadata))
                        } else {
                            None
                        }
                    })
            })
        })
    }

    //  Gets the Offset of the slice.
    //
    //  If the entry doesn't already exists, create it if possible, returning an error if insertion is not possible.
    //
    //  #   Safety
    //
    //  This `director` must have been used for all previous insertions in this instance.
    unsafe fn insert<A>(
        &self,
        hash: u64,
        slice: &[u8],
        store: &Store,
        director: &ShardDirector<A>,
    ) -> Result<Offset, InternerError>
    where
        A: Allocator,
    {
        for (part, atomic) in self.0.iter().enumerate() {
            let part = PartIndex(part);

            let groups = atomic.load(Ordering::Relaxed);

            let groups = if let Some(groups) = NonNull::new(groups) {
                groups
            } else {
                self.try_allocate(part, director)?
            };

            let number_groups = director.groups_of(part);

            //  Safety:
            //  -   `groups` is valid for reads & (sync) writes for `number_groups` elements.
            //  -   `groups` is pointing to `number_groups` initialized elements.
            //  -   There will be no mutable reference to this memory for the lifetime of `groups`.
            //  -   The total size is less than `isize::MAX`, as the allocation succeeded.
            let groups = unsafe { core::slice::from_raw_parts(groups.as_ptr(), number_groups) };

            //  Safety:
            //  -   This  `director` was used for all previous insertions.
            let result = unsafe { Self::insert_in_part(groups, hash, slice, store, director) };

            match result {
                Err(InternerError::KeyMapExhausted) => continue,
                result => return result,
            }
        }

        Err(InternerError::KeyMapExhausted)
    }

    //  Gets the Offset of the slice.
    //
    //  If the entry doesn't already exists, create it if possible, returning an error if insertion is not possible.
    //
    //  #   Safety
    //
    //  This `director` must have been used for all previous insertions in this instance.
    unsafe fn insert_in_part<A>(
        groups: &[MapGroup],
        hash: u64,
        slice: &[u8],
        store: &Store,
        director: &ShardDirector<A>,
    ) -> Result<Offset, InternerError>
    where
        A: Allocator,
    {
        debug_assert_eq!(
            1,
            groups.len().count_ones(),
            "Expected `groups` to have a power-of-2 size"
        );

        let (_, residual, initial) = director.split_hash(hash);

        for offset in PROBING_SEQUENCE {
            let index = ((initial + offset) & (groups.len() as u64 - 1)) as usize;

            //  Safety:
            //  -   `index` is less then `groups.len()` due to the cropping.
            let group = unsafe { groups.get_unchecked(index) };

            //  Safety:
            //  -   This `director` was used for all previous insertions in `group` and `store`.
            let result = unsafe { Self::insert_in_group(group, residual, slice, store, director) };

            match result {
                Err(InternerError::KeyMapExhausted) => continue,
                result => return result,
            }
        }

        Err(InternerError::KeyMapExhausted)
    }

    //  Gets the Offset of the slice.
    //
    //  If the entry doesn't already exists, create it if possible, returning an error if insertion is not possible.
    //
    //  #   Safety
    //
    //  This `director` must have been used for all previous insertions in this instance and `store`.
    unsafe fn insert_in_group<A>(
        group: &MapGroup,
        residual: u8,
        slice: &[u8],
        store: &Store,
        director: &ShardDirector<A>,
    ) -> Result<Offset, InternerError>
    where
        A: Allocator,
    {
        debug_assert_ne!(0, residual);
        debug_assert!(residual < 128);
        debug_assert_eq!(group.header.len(), group.elements.len());

        let locked = residual | 0x80;

        //  TODO: header search can be SIMD accelerated.
        for (header, element) in group.header.iter().zip(group.elements.iter()) {
            let mut h = header.load(Ordering::Acquire);

            if h == 0 {
                match header.compare_exchange(h, locked, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => {
                        //  Safety:
                        //  -   This `director` was used for all previous insertions in `store.
                        let result = unsafe { store.push_slice(slice, director) };

                        match result {
                            Ok(offset) => {
                                element.store(offset.0.get(), Ordering::Relaxed);
                                header.store(residual, Ordering::Release);
                                return Ok(offset);
                            }
                            Err(e) => {
                                header.store(0, Ordering::Relaxed);
                                return Err(e);
                            }
                        }
                    }
                    //  Failed to insert, need to check what else was inserted.
                    Err(new_h) => h = new_h,
                }

                //  fallthrough.
            }

            //  Another thread is attempting to insert a suspiciously similar slice, need to wait until they're done.
            if h == locked {
                loop {
                    //  Famous last words: it should take too long to perform the insertion, right?
                    hint::spin_loop();

                    h = header.load(Ordering::Acquire);

                    if h != locked {
                        break;
                    }
                }

                debug_assert_eq!(h, residual);

                //  fallthrough.
            }

            if h == residual {
                let offset = element.load(Ordering::Relaxed);
                debug_assert_ne!(0, offset);

                //  Safety:
                //  -   Only Offsets are inserted, and Offsets are only non-zero.
                let offset = unsafe { NonZeroU32::new_unchecked(offset) };

                let offset = Offset(offset);

                //  The offset, however, may very well point to a different slice. Pidgeon Hole principle and all that.

                //  Safety:
                //  -   `offset` was obtained from this `store`, since there's a 1-to-1 store-map mapping in a shard.
                //  -   The `store` was not reset since `offset` was obtained, otherwise the `map` would have been
                //      reset too.
                //  -   This `director` was used for allocations in the `store`.
                let candidate = unsafe { store.get_slice_unchecked(offset, director) };

                if candidate == slice {
                    return Ok(offset);
                }

                //  fallthrough.
            }

            //  Not found, let's move on.
        }

        Err(InternerError::KeyMapExhausted)
    }

    //  Tries to allocate memory, returns an error if allocation failed.
    fn try_allocate<A>(&self, part: PartIndex, director: &ShardDirector<A>) -> Result<NonNull<MapGroup>, InternerError>
    where
        A: Allocator,
    {
        let mut groups = director.allocate_groups(part)?;

        let current = ptr::null_mut();

        if let Err(p) = self.0[part.0].compare_exchange(current, groups.as_ptr(), Ordering::Relaxed, Ordering::Relaxed)
        {
            //  Safety:
            //  -   Freshly allocated.
            unsafe { director.deallocate_groups(groups, part) };

            //  Safety:
            //  -   Non-null, or `compare_exchange` would have succeeded.
            groups = unsafe { NonNull::new_unchecked(p) }
        };

        Ok(groups)
    }
}

//  Safety:
//  -   A map is safe to send across threads, and safe to access concurrently from multiple threads.
unsafe impl Send for Map {}
unsafe impl Sync for Map {}

#[cfg(test)]
mod tests {
    use alloc::alloc::Global;

    use super::*;

    fn ensure_send<T: Send>() {}
    fn ensure_sync<T: Sync>() {}

    #[test]
    fn shard_send() {
        ensure_send::<Shard>();
    }

    #[test]
    fn shard_sync() {
        ensure_sync::<Shard>();
    }

    #[test]
    fn store_append_small() {
        //  Checks that a small allocation fits into the first part.

        const SLICE: &[u8] = b"Allo";

        let store = TestStore::new(8);

        let offset = store.push_slice(SLICE).expect("Success");

        assert_eq!(4, offset.0.get());

        //  Safety:
        //  -   `offset` was obtained from `store`.
        //  -   `store.store` was not reset since `offset` was obtained.
        let actual = unsafe { store.get_slice(offset) };

        assert_eq!(SLICE, actual);
    }

    #[test]
    fn store_append_too_big_for_first() {
        //  Checks that a larger allocation may require offloading to a larger part.

        const SLICE: &[u8] = b"Hello";

        let store = TestStore::new(8);

        let offset = store.push_slice(SLICE).expect("Success");

        assert_eq!(20, offset.0.get());

        //  Safety:
        //  -   `offset` was obtained from `store`.
        //  -   `store.store` was not reset since `offset` was obtained.
        let actual = unsafe { store.get_slice(offset) };

        assert_eq!(SLICE, actual);
    }

    #[test]
    fn store_append_multi() {
        //  Checks that multiple slices can be inserted and retrieved.

        const SLICES: &[&[u8]] = &[
            b"Hello, World",
            b"Pfft",
            b"Arsene Lupin, gentleman cambrioleur",
            b"i",
            b"foo",
        ];

        let store = TestStore::new(8);

        let offsets: Vec<_> = SLICES
            .iter()
            .map(|slice| store.push_slice(slice).expect("Success"))
            .collect();

        assert_eq!(20, offsets[0].0.get()); //  3rd part, offset by slice length.
        assert_eq!(4, offsets[1].0.get()); //  1st part, offset by slice length.
        assert_eq!(68, offsets[2].0.get()); //  5th part, offset by slice length.
        assert_eq!(12, offsets[3].0.get()); //  2nd part, offset by slice length.
        assert_eq!(36, offsets[4].0.get()); //  4th part, offset by slice length.

        for (expected, offset) in SLICES.iter().zip(offsets) {
            //  Safety:
            //  -   `offset` was obtained from `store`.
            //  -   `store.store` was not reset since `offset` was obtained.
            let actual = unsafe { store.get_slice(offset) };

            assert_eq!(*expected, actual);
        }
    }

    #[test]
    fn store_append_too_big_for_any() {
        //  Checks that a very large allocation may not be suitable at all.

        let store = TestStore::new(8);

        let maximum_part_capacity =
            store.director.bytes_of(PartIndex(JAGGED_LENGTH - 1)) - mem::size_of::<SliceLength>();

        let too_big = vec![0xef; maximum_part_capacity + 1];

        let result = store.push_slice(&too_big);

        assert_eq!(Err(InternerError::ByteStorageExhausted), result);
    }

    struct TestStore<A = Global>
    where
        A: Allocator,
    {
        director: ShardDirector<A>,
        store: Store,
    }

    impl TestStore<Global> {
        //  Creates an instance, inference-friendly.
        fn new(number_bytes: usize) -> Self {
            Self::with_allocator(number_bytes, Global)
        }
    }

    impl<A> TestStore<A>
    where
        A: Allocator,
    {
        //  Creates an instance.
        fn with_allocator(number_bytes: usize, allocator: A) -> Self {
            let log_number_shards = 4;
            let log_initial_bytes = number_bytes.ilog2() as u8;
            let log_initial_groups = 3;

            let director = ShardDirector::new(log_number_shards, log_initial_bytes, log_initial_groups, allocator);
            let store = Store::default();

            Self { director, store }
        }

        //  Gets the slice associated to the offset.
        //
        //  #   Safety
        //
        //  -   `offset` must have been returned to this instance.
        //  -   The underlying `store` must not have been reset since `offset` was returned.
        unsafe fn get_slice(&self, offset: Offset) -> &[u8] {
            //  Safety:
            //  -   `offset` has been returned from `self.store`.
            //  -   `self.store` has not been reset since `offset` was returned.
            //  -   This `director` has been used for all previous allocations.
            unsafe { self.store.get_slice_unchecked(offset, &self.director) }
        }

        //  Pushes a slice, returning its offset, or an error if returning it was not possible.
        fn push_slice(&self, slice: &[u8]) -> Result<Offset, InternerError> {
            //  Safety:
            //  -   This `director` has been used for all previous allocations.
            unsafe { self.store.push_slice(slice, &self.director) }
        }
    }

    impl<A> Drop for TestStore<A>
    where
        A: Allocator,
    {
        fn drop(&mut self) {
            //  Safety:
            //  -   This `director` has been used for all allocations.
            unsafe { self.store.reset(&self.director) };
        }
    }

    #[test]
    fn map_insert_first() {
        //  Checks that a single item can be inserted in an empty Map.

        const SLICE: &[u8] = b"Allo";
        const HASH: u64 = 0;

        let map = TestMap::new(8, 128);

        let offset = map.insert(HASH, SLICE).expect("Success");

        assert_eq!(4, offset.0.get());
    }

    #[test]
    fn map_insert_duplicates() {
        //  Checks that even after multiple insertions, duplicates are correctly de-duplicated.

        const SLICES: &[&[u8]] = &[b"Allo", b"Baby", b"Cassonade"];
        const HASH: u64 = 0;

        let map = TestMap::new(8, 128);

        let offsets: Vec<Offset> = SLICES
            .iter()
            .map(|slice| map.insert(HASH, slice).expect("Success"))
            .collect();

        assert_eq!(4, offsets[0].0.get());
        assert_eq!(12, offsets[1].0.get());
        assert_eq!(20, offsets[2].0.get());

        let re_offsets: Vec<Offset> = SLICES
            .iter()
            .map(|slice| map.insert(HASH, slice).expect("Success"))
            .collect();

        assert_eq!(offsets, re_offsets);
    }

    #[test]
    #[cfg(not(miri))] //  Too long in MIRI.
    fn map_insert_many_collisions() {
        //  Checks that even in the presence of many collisions, different slices still get different offsets.

        //  Simulating a _really_ bad hash function.
        const HASH: u64 = 0;

        //  16 entries initially, means a _single_ group initially.
        let map = TestMap::new(8, 16);

        let mut offsets = Vec::new();

        //  This nested loop will generate enough variant strings to fill up 42 groups.
        for first in b'a'..=b'z' {
            for second in b'a'..=b'z' {
                let array = [first, second];

                offsets.push(map.insert(HASH, &array).expect("Success"));
            }
        }

        assert!(
            offsets.windows(2).all(|duo| duo[0].0.get() < duo[1].0.get()),
            "Expected offsets to be unique, but got {offsets:?}"
        );
    }

    struct TestMap<A = Global>
    where
        A: Allocator,
    {
        director: ShardDirector<A>,
        store: Store,
        map: Map,
    }

    impl TestMap<Global> {
        //  Creates an instance, inference-friendly.
        fn new(number_bytes: usize, number_entries: usize) -> Self {
            Self::with_allocator(number_bytes, number_entries, Global)
        }
    }

    impl<A> TestMap<A>
    where
        A: Allocator,
    {
        //  Creates an instance.
        fn with_allocator(number_bytes: usize, number_entries: usize, allocator: A) -> Self {
            let log_number_shards = 4;
            let log_initial_bytes = number_bytes.ilog2() as u8;
            let log_initial_groups = (number_entries / GROUP_LENGTH).ilog2() as u8;

            let director = ShardDirector::new(log_number_shards, log_initial_bytes, log_initial_groups, allocator);
            let store = Store::default();
            let map = Map::default();

            Self { director, store, map }
        }

        //  Intern the slice in the map.
        fn insert(&self, hash: u64, slice: &[u8]) -> Result<Offset, InternerError> {
            //  Safety:
            //  -   This `director` has been used for all previous insertions in this instance and `store`.
            unsafe { self.map.insert(hash, slice, &self.store, &self.director) }
        }
    }

    impl<A> Drop for TestMap<A>
    where
        A: Allocator,
    {
        fn drop(&mut self) {
            //  Safety:
            //  -   This `director` has been used for all allocations.
            unsafe {
                self.map.reset(&self.director);
                self.store.reset(&self.director);
            }
        }
    }
} // mod tests
