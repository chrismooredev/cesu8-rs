
use std::hash::Hash;

use super::mutf8string::Mutf8String;
use super::{BaseCesu8StrEncoding, Cesu8StrEncoding, BaseCesu8StringEncoding};

/// A borrowed MUTF-8 string.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Mutf8Str {
    inner: [u8],
}

impl BaseCesu8StrEncoding for Mutf8Str {
    const ENCODE_NUL: bool = true;
    const NUL_TERM: bool = false;

    /// Uses pointer magic to transmute a byte slice to an instance of Mutf8Str
    /// 
    /// # Safety
    /// The byte string should be encoded in MUTF8. That is, UTF8 with 4-byte-sequences re-encoded as 2, 3-byte
    /// sequences, and with nul bytes re-encoded as as [0xC0, 0x80]
    unsafe fn _from_bytes_unchecked(bytes: &[u8]) -> &Self {
        // &[u8]
        // *const [u8]
        // *const Mutf8Str
        // &Mutf8Str

        // should be a no-op

        &*(bytes as *const [u8] as *const Self)
    }
    
    fn _raw_bytes(&self) -> &[u8] {
        unsafe { &*(self as *const Self as *const [u8]) }
    }
}
impl Cesu8StrEncoding for Mutf8Str {

}

// don't impl Deref as it can make nul-terminator inclusion ambiguous for Mutf8CStr -> Mutf8Str -> [u8]
// impl Deref for Mutf8Str {
//     type Target = [u8];
//     fn deref(&self) -> &Self::Target {
//         self.as_bytes()
//     }
// }
impl ToOwned for Mutf8Str {
    type Owned = Mutf8String;
    fn to_owned(&self) -> Self::Owned {
        // SAFETY: string has already been validated as mutf8
        unsafe { Self::Owned::from_bytes_unchecked(self.inner.to_vec()) }
    }
}
impl Hash for Mutf8Str {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write(self.as_bytes());
        state.write_u8(0xff);
    }
}
impl Default for &Mutf8Str {
    fn default() -> Self {
        const EMPTY: &[u8] = &[];
        unsafe { Mutf8Str::from_bytes_unchecked(EMPTY) }
    }
}

