use std::borrow::Borrow;
use std::ops::Deref;
use std::borrow::Cow;
use std::str;

use super::prelude::*;

/// The error when trying to create a Mutf8CString from a byte buffer.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FromMutf8BytesWithNulError {
    kind: NGCesu8CError,
    bytes: Vec<u8>,
}
impl FromMutf8BytesWithNulError {
    /// The specific error encountered when trying to create a Mutf8CString from a byte buffer.
    pub fn kind(&self) -> &NGCesu8CError {
        &self.kind
    }
    /// The raw source bytes for the conversion, that caused the error.
    /// 
    /// Using [`FromMutf8BytesWithNulError::into_bytes`] over `FromMutf8BytesWithNulError::as_bytes` allows recovering
    /// the initial allocation.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
    /// The raw source bytes for the conversion, that caused the error.
    /// 
    /// Using `FromMutf8BytesWithNulError::into_bytes` over [`FromMutf8BytesWithNulError::as_bytes`] allows recovering
    /// the initial allocation.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

/// An owned Mutf8 byte buffer, with a terminating nul byte.
/// 
/// This can be safely converted into a pointer for usage with JNI with [`Mutf8CStr::as_ptr()`]
#[derive(PartialEq, Eq, Clone)]
pub struct Mutf8CString {
    pub(crate) inner: Vec<u8>,
}
impl Mutf8CString {
    impl_string_encoding_meths!(base);
    impl_string_encoding_meths!(cstring);
}

impl Mutf8CString {
    pub(crate) unsafe fn _from_bytes_unchecked(v: Vec<u8>) -> Self {
        Self { inner: v }
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


// heavily adjusted copies from std::ffi::CString
impl Mutf8CString {
    /// Creates a new C-compatible Mutf8 string from a container of bytes.
    ///
    /// This function will consume the provided data and use the
    /// underlying bytes to construct a new string, ensuring that
    /// there is a trailing 0 byte. This trailing 0 byte will be
    /// appended by this function; the provided data should *not*
    /// contain any 0 bytes in it. It will also ensure that it is
    /// in Mutf8 format.
    ///
    /// # Examples
    ///
    /// ```ignore (extern-declaration)
    /// use std::ffi::CString;
    /// use std::os::raw::c_char;
    ///
    /// extern "C" { fn puts(s: *const c_char); }
    ///
    /// let to_print = CString::new("Hello!").expect("CString::new failed");
    /// unsafe {
    ///     // TODO: make Mutf8 specific
    ///     puts(to_print.as_ptr());
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// This function will return an error if the supplied bytes contain an
    /// internal 0 byte. The [`FromMutf8BytesWithNulError`] returned will
    /// contain the bytes as well as the position of the error.
    #[inline]
    pub fn new<T: Into<Vec<u8>>>(t: T) -> Result<Mutf8CString, NGCesu8CError> {
        // the std::ffi::CString::new impl uses specialization, which aren't available outside of stdlib(?)

        fn from_bytes(mut b: Vec<u8>) -> Result<Mutf8CString, NGCesu8CError> {
            b.reserve_exact(1);
            b.push(b'\0');
            Mutf8CStr::from_bytes_with_nul(&b)
                .map(|_| ()) // drop the borrowed Mutf8CStr, knowing it was successful
                .map(move |_| Mutf8CString { inner: b })
        }

        from_bytes(t.into())
    }
}

// TODO: AsRef<Mutf8CStr>
impl Borrow<Mutf8CStr> for Mutf8CString {
    fn borrow(&self) -> &Mutf8CStr {
        self
    }
}
impl Default for Mutf8CString {
    fn default() -> Self {
        let a: &Mutf8CStr = Default::default();
        a.to_owned()
    }
}
impl Deref for Mutf8CString {
    type Target = Mutf8CStr;
    fn deref(&self) -> &Self::Target {
        unsafe { Mutf8CStr::from_bytes_with_nul_unchecked(&self.inner) }
    }
}
impl Drop for Mutf8CString {
    fn drop(&mut self) {
        // SAFETY: an Mutf8CString must contain at least one value, the nul terminator
        // set inner[0] to zero to follow the impl of std::ffi::CString::drop
        unsafe {
            *self.inner.get_unchecked_mut(0) = 0;
        }
    }
}
