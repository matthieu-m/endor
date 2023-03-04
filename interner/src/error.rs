/// Errors from the library.
use core::{error, fmt};

/// Errors returned by this library.
#[derive(Clone, Debug)]
pub enum InternerError {
    /// The `BytesId` or `StringId` is not from this instance of `Interner`.
    IdMismatch,
    /// The pool of interner `Id` has been exhausted.
    IdPoolExhausted,
    /// The byte storage of the Shard has been exhausted.
    ByteStorageExhausted,
    /// The set of the Shard has been exhausted.
    KeyMapExhausted,
    /// No memory could be allocated.
    MemoryExhausted,
}

impl fmt::Display for InternerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{:?}", self)
    }
}

impl error::Error for InternerError {}
