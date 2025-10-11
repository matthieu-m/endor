//! The layout of a thin pointer memory block.

use core::{
    alloc::{Layout, LayoutError},
    hint,
    ptr::{self, NonNull, Pointee},
};

/// The layout of the thin pointer memory block.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ThinLayout {
    //  Layout of the entire block.
    block: Layout,
    //  Backward offsets from thin pointer.
    metadata_offset: usize,
    header_offset: usize,
    allocator_offset: usize,
    start_offset: usize,
}

impl ThinLayout {
    /// Constructs a new instance.
    ///
    /// #   Layout Invariance
    ///
    /// The choice of `T` has no effect on the resulting `metadata_offset`, `header_offset`, nor `allocator_offset`.
    /// Therefore these offsets may be consulted by substituting `()` for `T`.
    ///
    /// The choice of `A` has no effect on the resulting `metadata_offset`, nor `header_offset`. Therefore these offsets
    /// may be consulted by substituting `()` for `A`.
    ///
    /// Combining the above, this means that `ThinLayout::new::<(), H, U, ()>()` will yield compatible header & metadata
    /// offsets, suitable for accessing the header or metadata.
    pub const fn new<T, H, U, A>() -> Self
    where
        U: ?Sized,
    {
        //  The compiler will error if this type cannot be represented (too large).
        #[allow(dead_code)]
        struct Block<T, H, U, A>(T, ((<U as Pointee>::Metadata, H), Packed<A>))
        where
            U: ?Sized;

        let data = Layout::new::<T>();
        let metadata = Layout::new::<<U as Pointee>::Metadata>();
        let header = Layout::new::<H>();
        let allocator = Layout::new::<Packed<A>>();

        let Ok(this) = Self::compute_layout(data, metadata, header, allocator) else {
            //  Safety:
            //  -   The compiler did not error on `Block`, therefore the layout will not overflow.
            unsafe { hint::unreachable_unchecked() }
        };

        debug_assert!(Layout::new::<Block<T, H, U, A>>().size() == this.block().size());
        debug_assert!(Layout::new::<Block<T, H, U, A>>().align() == this.block().align());

        this
    }

    /// Constructs a new instance from a raw value.
    pub const fn for_value<T, H, A>(value: &T) -> Result<Self, LayoutError>
    where
        T: ?Sized,
    {
        let data = Layout::for_value::<T>(value);
        let metadata = Layout::new::<<T as Pointee>::Metadata>();
        let header = Layout::new::<H>();
        let allocator = Layout::new::<Packed<A>>();

        Self::compute_layout(data, metadata, header, allocator)
    }

    /// Returns the layout of the complete block.
    pub const fn block(&self) -> Layout {
        self.block
    }

    /// Returns the offset between the start of the pointee metadata field and the start of the data field.
    ///
    /// A pointer to the pointee metadata field can be obtained by removing this offset from the location pointed to by
    /// the thin pointer.
    pub const fn metadata_offset(&self) -> usize {
        self.metadata_offset
    }

    /// Returns the offset between the start of the header field and the start of the data field.
    ///
    /// A pointer to the header field can be obtained by removing this offset from the location pointed to by the
    /// thin pointer.
    pub const fn header_offset(&self) -> usize {
        self.header_offset
    }

    /// Returns the offset between the start of the allocator field and the start of the data field.
    ///
    /// A pointer to the allocator field can be obtained by removing this offset from the location pointed to by
    /// the thin pointer.
    pub const fn allocator_offset(&self) -> usize {
        self.allocator_offset
    }

    /// Returns the offset between the start of the block and the start of the data field.
    ///
    /// A pointer to the start of the block can be obtained by removing this offset from the location pointed to by
    /// the thin pointer.
    pub const fn start_offset(&self) -> usize {
        self.start_offset
    }

    /// Returns a suitably aligned dangling pointer.
    pub const fn dangling(&self) -> NonNull<u8> {
        //  Not only should a dangling pointer be non-null, it should also allow deriving non-null pointers to the
        //  allocator, metadata, and header.
        //
        //  This means that _just_ taking the start-offset is not enough:
        //
        //  -   if 0, then a null pointer is returned.
        //  -   if non-0, then in the absence of padding and allocator, the metadata may still be at offset 0.

        //  If start-offset is 0, then computing the pointer to the metadata or header will preserve the pointer,
        //  so all we need is to ensure a non-zero pointer suitably aligned for the data block.
        if self.start_offset == 0 {
            return self.block.dangling();
        }

        //  Otherwise, the simplest solution is to take twice the start offset, which necessarily preserves the
        //  alignments.
        let dangling = ptr::without_provenance_mut(self.start_offset * 2);

        //  Safety:
        //  -   NonNull: `self.start_offset` is non-zero, and fits within `isize`, therefore `self.start_offset * 2` is
        //      non-zero, and does not wrap.
        unsafe { NonNull::new_unchecked(dangling) }
    }
}

//
//  Implementation
//

impl ThinLayout {
    const fn compute_layout(
        data: Layout,
        metadata: Layout,
        header: Layout,
        allocator: Layout,
    ) -> Result<Self, LayoutError> {
        let (hm, hm_offset) = match metadata.extend(header) {
            Ok(extended) => extended,
            Err(e) => return Err(e),
        };

        let (fh, fh_offset) = match hm.extend(allocator) {
            Ok(extended) => extended,
            Err(e) => return Err(e),
        };

        let (unaligned_block, block_offset) = match fh.extend(data) {
            Ok(extended) => extended,
            Err(e) => return Err(e),
        };

        let block = unaligned_block.pad_to_align();
        let metadata_offset = metadata.size();
        let header_offset = hm_offset + header.size();
        let allocator_offset = fh_offset + allocator.size();
        let start_offset = block_offset + (block.size() - unaligned_block.size());

        Ok(Self {
            block,
            metadata_offset,
            header_offset,
            allocator_offset,
            start_offset,
        })
    }
}

#[repr(C, packed(1))]
struct Packed<T>(T);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn brush_sized() {
        let layout = ThinLayout::new::<[u32; 4], u8, [u32; 4], Allocator>();

        assert_eq!((28, 4), (layout.block().size(), layout.block().align()));
        assert_eq!(0, layout.metadata_offset());
        assert_eq!(1, layout.header_offset());
        assert_eq!(9, layout.allocator_offset());
        assert_eq!(12, layout.start_offset());
    }

    #[test]
    fn brush_slice() {
        let layout = ThinLayout::new::<[u32; 4], usize, [u32], Allocator>();

        assert_eq!((40, 8), (layout.block().size(), layout.block().align()));
        assert_eq!(8, layout.metadata_offset());
        assert_eq!(16, layout.header_offset());
        assert_eq!(24, layout.allocator_offset());
        assert_eq!(24, layout.start_offset());
    }

    #[test]
    fn data_invariance() {
        #[track_caller]
        fn assert_invariant<H, U, A>()
        where
            U: ?Sized,
        {
            let with_allocator = ThinLayout::new::<[u32; 4], H, U, A>();
            let without_allocator = ThinLayout::new::<(), H, U, A>();

            assert_eq!(with_allocator.header_offset(), without_allocator.header_offset());
            assert_eq!(with_allocator.metadata_offset(), without_allocator.metadata_offset());
            assert_eq!(with_allocator.allocator_offset(), without_allocator.allocator_offset());
        }

        assert_invariant::<usize, [u32; 4], Allocator>();
        assert_invariant::<(), [u32; 4], Allocator>();

        assert_invariant::<usize, [u32], Allocator>();
        assert_invariant::<(), [u32], Allocator>();
    }

    #[test]
    fn allocator_invariance() {
        #[track_caller]
        fn assert_invariant<T, H, U>()
        where
            U: ?Sized,
        {
            let with_allocator = ThinLayout::new::<T, H, U, Allocator>();
            let without_allocator = ThinLayout::new::<T, H, U, ()>();

            assert_eq!(with_allocator.header_offset(), without_allocator.header_offset());
            assert_eq!(with_allocator.metadata_offset(), without_allocator.metadata_offset());
        }

        assert_invariant::<[u32; 4], usize, [u32; 4]>();
        assert_invariant::<[u32; 4], (), [u32; 4]>();

        assert_invariant::<[u32; 4], usize, [u32]>();
        assert_invariant::<[u32; 4], (), [u32]>();
    }

    //  Dummy allocator.
    #[allow(dead_code)]
    struct Allocator(usize);
} // mod tests
