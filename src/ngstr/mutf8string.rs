use std::borrow::Borrow;
use std::ops::Deref;

use super::mutf8str::Mutf8Str;
use super::preamble::*;


#[derive(PartialEq, Eq, Clone, Default)]
pub struct Mutf8String {
    pub(crate) inner: Vec<u8>,
}

impl Mutf8String {
    impl_string_encoding_meths!(base);
    impl_string_encoding_meths!(string);
}

impl Mutf8String {
    pub(crate) unsafe fn _from_bytes_unchecked(b: Vec<u8>) -> Self {
        Mutf8String { inner: b }
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

impl Borrow<Mutf8Str> for Mutf8String {
    fn borrow(&self) -> &Mutf8Str {
        self
    }
}
impl Deref for Mutf8String {
    type Target = Mutf8Str;
    fn deref(&self) -> &Self::Target {
        // SAFETY: this type should only contain valid mutf8
        unsafe { Self::Target::_from_bytes_unchecked(&self.inner) }
    }
}
