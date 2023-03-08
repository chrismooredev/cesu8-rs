use std::borrow::Borrow;
use std::ops::Deref;
use std::borrow::Cow;
use std::str;
use std::fmt;
use std::hash::Hash;

use crate::Variant;
use crate::ngstr::Cesu8CStrEncoding;

use super::BaseCesu8StringEncoding;
use super::Cesu8CStringEncoding;
use super::NGCesu8CError;
use super::mutf8cstr::Mutf8CStr;

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
    inner: Vec<u8>,
}
impl BaseCesu8StringEncoding for Mutf8CString {
    unsafe fn _from_bytes_unchecked(v: Vec<u8>) -> Self {
        Self { inner: v }
    }

    fn _into_bytes_unchecked(self) -> Vec<u8> {
        // taken from std::ffi::CString::into_inner

        // Rationale: `mem::forget(self)` invalidates the previous call to `ptr::read(&self.inner)`
        // so we use `ManuallyDrop` to ensure `self` is not dropped.
        // Then we can return the box directly without invalidating it.
        // See https://github.com/rust-lang/rust/issues/62553.
        let this = std::mem::ManuallyDrop::new(self);
        unsafe { std::ptr::read(&this.inner) }
    }

}
impl Cesu8CStringEncoding for Mutf8CString {
}

// custom impls
impl Mutf8CString {

    /// Accepts a closure letting one adjust the raw mutf8 buffer.
    /// 
    /// If changes to the size are needed, you may want to ensure an extra byte is reserved at the end for a nul-terminator.
    /// 
    /// # Safety
    /// The provided vector should remain as valid mutf8 after editing, or through unwinds.
    /// 
    /// Namely, Nul bytes should not be inserted by this function, or 4-byte utf8 sequences.
    #[doc(hidden)]
    pub(crate) unsafe fn with_self_as_vec<F: FnOnce(&mut Vec<u8>)>(&mut self, f: F) {
        // replace 
        let inner_bs = std::mem::replace(&mut self.inner, Vec::new());

        // turn our Box<[u8]> to a Vec
        let mut inner = inner_bs;
        let popped = inner.pop(); // temporarily remove nul-terminator
        debug_assert_eq!(popped, Some(b'\0')); // assert we did grab a nul-terminator

        // TOOD: unwind handling?
        f(&mut inner);

        if cfg!(debug_assertions) {
            // on debug, assert the user kept inner as an mutf8 string
            let _ = crate::decoding::cesu8_validate::<true>(&inner).expect("invalid cesu8 in cesu8 slice");
        }

        // re-append our nul-terminator
        inner.reserve_exact(1);
        inner.push(b'\0');

        // take our non-alloc Vec back out
        let _ = std::mem::replace(&mut self.inner, inner);
    }

    /// Extends the current [`Mutf8CString`] with the contents of a pre-validated mutf8 string slice.
    /// 
    /// # Safety
    /// The contained byte slice must be in valid mutf8, without any nul bytes. (They should be encoded)
    pub unsafe fn extend_from_mutf8_with_bytes<'a, F: FnMut() -> Cow<'a, [u8]>>(&mut self, mut f: F) {
        unsafe { Self::with_self_as_vec(self, |v| {
            let nslice = f();
            v.reserve_exact(nslice.len() + 1);
            v.extend_from_slice(&nslice);
        })}
    }

    /// Extends the current [`Mutf8CString`] with the contents of another [`Mutf8CStr`]
    pub fn extend_from_mutf8(&mut self, string: &Mutf8CStr) {
        if string.is_empty() { return; }
        unsafe { Self::with_self_as_vec(self, |v| {
            let nslice = string.to_bytes();
            v.reserve_exact(nslice.len() + 1);
            v.extend_from_slice(nslice);
        })}
    }

    /// Push a UTF-8 [`&str`] onto the end of an [`Mutf8CString`], re-encoding if necessary
    /// 
    /// The passed string should not have a nul terminator, unless a zero terminated character at the end is a part of the expected data.
    pub fn extend_from_str(&mut self, string: &str) {
        unsafe { Self::with_self_as_vec(self, |v| {
            // encode the string directly into our own allocation, growing if needed
            // the returned result returns a utf8 error, which is irrelavent when writing to an mutf8 buffer
            let _ = crate::encoding::utf8_to_cesu8_safe(string, v, Variant::Java);
        }) }
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
impl fmt::Debug for Mutf8CString {
    fn fmt(&self, f: &'_ mut fmt::Formatter<'_>) -> fmt::Result {
        let rs_str = Mutf8CStr::to_string(self);
        write!(f, "{rs_str:?}")
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
impl fmt::Display for Mutf8CString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: turn this into a more iterator-focused view, possibly stack allocate
        let rs_str = Mutf8CStr::to_string(self);
        write!(f, "{rs_str:}")
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
impl ToOwned for Mutf8CStr {
    type Owned = Mutf8CString;
    fn to_owned(&self) -> Self::Owned {
        Mutf8CString { inner: self.to_bytes_with_nul().into() }
    }
}
impl Hash for Mutf8CString {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}
