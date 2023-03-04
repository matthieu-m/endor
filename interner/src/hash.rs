//  A quick hash algorithm, used by rustc and Firefox.
//
//  The exact algorithm was copied from `https://github.com/cbreeden/fxhash/blob/master/lib.rs`.
//
//  Note: unfortuately `fxhash` is not a `no_std` crate, so here we are.

use core::{
    hash::{BuildHasher, BuildHasherDefault, Hasher},
    mem,
    ops::BitXor,
    ptr,
};

/// A BuildHasher which returns a `Default` `FxHasher`.
pub type DefaultFxBuildHasher = BuildHasherDefault<FxHasher>;

/// A BuildHasher which returns a seeded `FxHasher`.
#[derive(Clone, Copy, Debug, Default)]
pub struct FxBuildHasher {
    seed: u64,
}

impl FxBuildHasher {
    /// Creates a new instance with this specific seed.
    ///
    /// All `FxHasher` created by this instance will start with their state initialized with this seed.
    #[inline(always)]
    pub fn new(seed: u64) -> Self {
        Self { seed }
    }
}

impl BuildHasher for FxBuildHasher {
    type Hasher = FxHasher;

    #[inline(always)]
    fn build_hasher(&self) -> Self::Hasher {
        FxHasher { hash: self.seed }
    }
}

/// A fast hashing algorithm, originally extracted from the rustc compiler and Firefox.
///
/// Similar in spirit to FNV, but hashing 8 bytes at a time whenever possible for greater speed.
///
/// This is NOT a cryptographic algorithm.
#[derive(Clone, Copy, Debug, Default)]
pub struct FxHasher {
    hash: u64,
}

impl Hasher for FxHasher {
    #[inline(always)]
    fn write(&mut self, bytes: &[u8]) {
        self.hash = write64(self.hash, bytes);
    }

    #[inline(always)]
    fn write_u8(&mut self, i: u8) {
        self.hash.hash_word(u64::from(i));
    }

    #[inline(always)]
    fn write_u16(&mut self, i: u16) {
        self.hash.hash_word(u64::from(i));
    }

    #[inline(always)]
    fn write_u32(&mut self, i: u32) {
        self.hash.hash_word(u64::from(i));
    }

    #[inline(always)]
    fn write_u64(&mut self, i: u64) {
        self.hash.hash_word(i);
    }

    #[inline(always)]
    fn write_usize(&mut self, i: usize) {
        self.hash.hash_word(i as u64);
    }

    #[inline(always)]
    fn finish(&self) -> u64 {
        self.hash
    }
}

//
//  Implementation
//

const ROTATE: u32 = 5;
const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

trait HashWord {
    fn hash_word(&mut self, word: Self);
}

impl HashWord for u64 {
    #[inline(always)]
    fn hash_word(&mut self, word: u64) {
        *self = self.rotate_left(ROTATE).bitxor(word).wrapping_mul(SEED);
    }
}

//  Make method available for inlining across crates.
#[inline]
fn write64(mut hash: u64, mut bytes: &[u8]) -> u64 {
    while let Some((word, new_bytes)) = read_u64(bytes) {
        hash.hash_word(word);
        bytes = new_bytes;
    }

    if let Some((word, new_bytes)) = read_u32(bytes) {
        hash.hash_word(u64::from(word));
        bytes = new_bytes;
    }

    if let Some((word, new_bytes)) = read_u16(bytes) {
        hash.hash_word(u64::from(word));
        bytes = new_bytes;
    }

    if let Some(&byte) = bytes.first() {
        hash.hash_word(u64::from(byte));
    }

    hash
}

#[inline(always)]
fn read_u64(bytes: &[u8]) -> Option<(u64, &[u8])> {
    //  Safety:
    //  -   All bit patterns are a valid u64.
    unsafe { read(bytes) }
}

#[inline(always)]
fn read_u32(bytes: &[u8]) -> Option<(u32, &[u8])> {
    //  Safety:
    //  -   All bit patterns are a valid u32.
    unsafe { read(bytes) }
}

#[inline(always)]
fn read_u16(bytes: &[u8]) -> Option<(u16, &[u8])> {
    //  Safety:
    //  -   All bit patterns are a valid u16.
    unsafe { read(bytes) }
}

//  Safety:
//  -   All bit patterns should be a valid value of `T`.
#[inline(always)]
unsafe fn read<T>(bytes: &[u8]) -> Option<(T, &[u8])>
where
    T: Copy,
{
    let length = mem::size_of::<T>();

    if bytes.len() < length {
        return None;
    }

    //  Safety:
    //  -   `bytes.as_ptr()` is valid for reads of `mem::size_of::<T>`.
    //  -   All bit patterns are a valid value of `T`.
    let result = unsafe { ptr::read_unaligned(bytes.as_ptr() as *const T) };

    //  Safety:
    //  -   `bytes.len() >= length`.
    //
    //  TODO: Replace length check and get_unchecked with `try_split_at` if it ever happens...
    let bytes = unsafe { bytes.get_unchecked(length..) };

    Some((result, bytes))
}
