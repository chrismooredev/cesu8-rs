
// keep four string variants of actual types --
// null_terminated * ref/owned

// use an enum to internally switch between them, and only expose methods that statically
// switch methods - effectively optimizing out the runtime checks for the specific variant

use crate::Cesu8Error;

/// An error type for creating a Cesu8/Mutf8 CStr/CString
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum NGCesu8CError {
    /// An interior nul byte was found within a CString. The contained usize is the index into the str/byte buffer.
    InteriorNul(usize),
    /// A function expected a buffer with a nul terminator, but could not find one
    NotNulTerminated,
    /// Encoding/Decoding error between UTF8, or CESU8
    Encoding(Cesu8Error),
}

pub(crate) mod mutf8cstr;
pub(crate) mod mutf8cstring;
mod cross_impls;

