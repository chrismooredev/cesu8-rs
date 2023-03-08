use std::borrow::Borrow;
use std::ops::Deref;

use super::{BaseCesu8StringEncoding, Cesu8StringEncoding};
use super::mutf8str::Mutf8Str;


#[derive(PartialEq, Eq, Clone, Default)]
pub struct Mutf8String {
    inner: Vec<u8>,
}

impl BaseCesu8StringEncoding for Mutf8String {
    unsafe fn _from_bytes_unchecked(b: Vec<u8>) -> Self {
        Mutf8String { inner: b }
    }

    fn _into_bytes_unchecked(self) -> Vec<u8> {
        self.inner
    }
}
impl Cesu8StringEncoding for Mutf8String {

}

impl Borrow<Mutf8Str> for Mutf8String {
    fn borrow(&self) -> &Mutf8Str {
        self
    }
}
impl Deref for Mutf8String {
    type Target = Mutf8Str;
    fn deref(&self) -> &Self::Target {
        use crate::ngstr::BaseCesu8StrEncoding;

        // SAFETY: this type should only contain valid mutf8
        unsafe { Self::Target::_from_bytes_unchecked(&self.inner) }
    }
}
