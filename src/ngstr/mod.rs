
// keep four string variants of actual types --
// null_terminated * ref/owned

// use an enum to internally switch between them, and only expose methods that statically
// switch methods - effectively optimizing out the runtime checks for the specific variant

use crate::Cesu8Error;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum NGCesu8CError {
    InteriorNul(usize),
    NotNulTerminated,
    Encoding(Cesu8Error),
}

pub(crate) mod mutf8cstr;
pub(crate) mod mutf8cstring;
mod cross_impls;

