
use super::prelude::*;

/// A borrowed MUTF-8 string.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Mutf8Str {
    inner: [u8],
}

impl Mutf8Str {
    impl_str_encoding_meths!(base, Mutf8Str, any, "MUTF-8");
    impl_str_encoding_meths!(str, Mutf8Str, any, "MUTF-8");
}

impl Mutf8Str {
    /// Determines if this string encoding uses literal nul bytes. If true, then literal nul bytes are not allowed
    /// within the string's contents.
    pub const ENCODE_NUL: bool = true;
    /// Determines if this string maintains a literal nul byte as a terminator. This makes it functionally equilavent
    /// to a [`CStr`], including any encoding guarantees provided by the string type.
    /// 
    /// If this is `true`, then [`Self::ENCODE_NUL`] must also be `true`.
    pub const NUL_TERM: bool = false;

    /// Uses pointer magic to transmute a byte slice to an instance of Mutf8Str
    /// 
    /// # Safety
    /// The byte string should be encoded in MUTF8. That is, UTF8 with 4-byte-sequences re-encoded as 2, 3-byte
    /// sequences, and with nul bytes re-encoded as as [0xC0, 0x80]
    pub(crate) const unsafe fn _from_bytes_unchecked(bytes: &[u8]) -> &Self {
        // &[u8]
        // *const [u8]
        // *const Mutf8Str
        // &Mutf8Str

        // should be a no-op

        &*(bytes as *const [u8] as *const Self)
    }
    
    pub(crate) const fn _raw_bytes(&self) -> &[u8] {
        unsafe { &*(self as *const Self as *const [u8]) }
    }
}

// don't impl Deref as it can make nul-terminator inclusion ambiguous for Mutf8CStr -> Mutf8Str -> [u8]
impl ToOwned for Mutf8Str {
    type Owned = Mutf8String;
    fn to_owned(&self) -> Self::Owned {
        // SAFETY: string has already been validated as mutf8
        unsafe { Self::Owned::from_bytes_unchecked(self.inner.to_vec()) }
    }
}
impl Default for &Mutf8Str {
    fn default() -> Self {
        const EMPTY: &[u8] = &[];
        unsafe { Mutf8Str::from_bytes_unchecked(EMPTY) }
    }
}

