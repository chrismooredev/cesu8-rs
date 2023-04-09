use std::borrow::Borrow;
use std::ops::Deref;


use crate::ngstr::prelude::*;

/// An owned CESU-8 encoded string.
/// 
/// See crate documentation for encoding details.
#[derive(PartialEq, Eq, Clone, Default)]
pub struct Cesu8String {
    pub(crate) inner: Vec<u8>,
}

impl Cesu8String {
    impl_string_encoding_meths!(base, "CESU-8");
    impl_string_encoding_meths!(string, "CESU-8");
}

impl Cesu8String {
    pub(crate) const unsafe fn _from_bytes_unchecked(b: Vec<u8>) -> Self {
        Cesu8String { inner: b }
    }

    pub(crate) const fn _into_bytes_unchecked(self) -> Vec<u8> {
        // taken from std::ffi::CString::into_inner

        // Rationale: `mem::forget(self)` invalidates the previous call to `ptr::read(&self.inner)`
        // so we use `ManuallyDrop` to ensure `self` is not dropped.
        // Then we can return the box directly without invalidating it.
        // See https://github.com/rust-lang/rust/issues/62553.
        let this = std::mem::ManuallyDrop::new(self);
        unsafe { std::ptr::read(&this.inner) }
    }
}

impl Borrow<Cesu8Str> for Cesu8String {
    fn borrow(&self) -> &Cesu8Str {
        self
    }
}
impl Deref for Cesu8String {
    type Target = Cesu8Str;
    fn deref(&self) -> &Self::Target {
        // SAFETY: this type should only contain valid mutf8
        unsafe { Self::Target::_from_bytes_unchecked(&self.inner) }
    }
}
