use std::borrow::Borrow;
use std::ffi::CStr;
use std::ops::Deref;
use std::borrow::Cow;
use std::str;
use std::fmt;
use std::ffi::c_char;
use std::hash::Hash;

use crate::Variant;

use super::NGCesu8CError;
use super::mutf8cstr::{Mutf8CStr, FromStrWithNulError};

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
    inner: Box<[u8]>,
}

// custom impls
impl Mutf8CString {
    /// Creates an empty Mutf8CString with the given capacity (plus one for a nul terminator)
    pub fn with_capacity(capacity: usize) -> Mutf8CString {
        let v = Vec::with_capacity(capacity + 1);
        // Safety: The string is empty so it is valid Mutf8. _from_mutf8_vec_unchecked will add the required nul-terminator.
        unsafe { Mutf8CString::_from_mutf8_vec_unchecked(v) }
    }

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
        let inner_bs = std::mem::replace(&mut self.inner, Vec::new().into_boxed_slice());

        // turn our Box<[u8]> to a Vec
        let mut inner = inner_bs.into_vec();
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

        // convert ourselves back to a boxed slice
        let inner_bs = inner.into_boxed_slice();

        // take our non-alloc Vec back out
        let _ = std::mem::replace(&mut self.inner, inner_bs);
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

    /// Allocates a new [`Mutf8CString`] from the contents of a borrowed utf8 [`prim@str`].
    pub fn from_utf8(s: &str) -> Mutf8CString {
        let mut mutf8c = Mutf8CString::with_capacity(crate::default_cesu8_capacity(s.len()));
        mutf8c.extend_from_str(s);
        mutf8c
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
                .map(move |_| Mutf8CString { inner: b.into_boxed_slice() })
        }

        from_bytes(t.into())
    }

    /// Converts the [`Mutf8CString`] into a [`String`]. The nul-terminator is not included in the returned String.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    /// 
    /// let mutf8 = vec![b'f', b'o', b'o'];
    /// let mutf8_c_string = Mutf8CString::new(mutf8).expect("Mutf8CString::new failed");
    /// assert_eq!(mutf8_c_string.into_string(), "foo");
    /// ```
    pub fn into_string(self) -> String {
        let mut mutf8c = self.into_bytes();
        let _nul = mutf8c.pop();
        debug_assert_eq!(_nul, Some(b'\0'), "Mutf8CString did not have nul terminator");

        let utf8_error = crate::decoding::cesu8_validate::<true>(&mutf8c)
            .expect("Mutf8CString did not contain valid MUTF8");

        let utf8 = crate::decoding::cesu8_to_utf8(&crate::Cesu8Str {
            variant: Variant::Java,
            utf8_error,
            bytes: Cow::Owned(mutf8c)
        });

        utf8

        // match self.to_string() {
        //     Cow::Borrowed(_) => {
        //         // string also happens to be valid UTF-8
        //         if cfg!(debug_assertions) {
        //             String::from_utf8(self.into_bytes()).expect("Mutf8CString contains invalid UTF-8, after checked utf8 status")
        //         } else {
        //             unsafe { String::from_utf8_unchecked(self.into_bytes()) }
        //         }
        //     },
        //     Cow::Owned(o) => {
        //         // string was not UTF-8, but was re-allocated in conversion
        //         // TODO: special case this to modify the allocation in-place.
        //         //       should get strictly smaller, so allocation shouldn't grow.
        //         //       the allocation is reusable.
        //         o
        //     },
        // }
    }

    /// Converts an owned string to an owned Mutf8CString, while attempting to preserve the allocation of the underlying
    /// string. Note that any nuls in this string, including any at the end of the string, will be encoded as part of
    /// the Mutf8 string - that is, nul-terminators are ignored, encoded, and a true nul-terminator is added.
    /// 
    /// This currently is only possible for strings under 256 bytes (once in Mutf8 encoding). If the encoded string
    /// ends up larger, then this function will allocate.
    pub fn from_string(s: String) -> Mutf8CString {
        // Attempts to re-use the allocation for strings that can fit within 256 bytes
        // Could this be converted to an in-memory conversion? 
        let buf: [u8; 256] = [0; 256];
        let mut c = std::io::Cursor::new(buf);
        let mutf8 = match unsafe { crate::encoding::utf8_to_cesu8_spec::<_, true>(s.as_str(), 0, &mut c) } {
            Ok(_) => {
                // good to go, copy new bytes to old allocation
                let len = c.position() as usize;
                let mut bytes = s.into_bytes();
                bytes.clear();
                bytes.extend_from_slice(&buf[..len]);
                bytes
            },
            Err(_e) => {
                // string bigger than allowed cesu8 bytes, create new allocation
                let mut v = Vec::with_capacity(crate::default_cesu8_capacity(s.len()+1));
                crate::encoding::utf8_to_cesu8_safe(s.as_str(), &mut v, Variant::Java).expect("std::io::Write into a Vec shouldn't error");
                v
            }
        };
        unsafe { Mutf8CString::_from_mutf8_vec_unchecked(mutf8) }
    }

}

// mostly copied from std::ffi::CString
impl Mutf8CString {
    /// Creates a C-compatible mutf8 string by consuming a byte vector,
    /// without checking for interior 0 bytes or mutf8 compatibility.
    ///
    /// Trailing 0 byte will be appended by this function.
    ///
    /// This method is equivalent to [`Mutf8CString::new`] except that no runtime
    /// assertion is made for mutf8 encoding or that `v` contains no 0 bytes, and it requires an
    /// actual byte vector, not anything that can be converted to one with Into.
    ///
    /// # Safety
    /// The provided byte buffer must not contain interior nuls and must be encoded to mutf8
    /// 
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    ///
    /// let raw = b"foo".to_vec();
    /// unsafe {
    ///     let mutf8_c_string = Mutf8CString::from_mutf8_vec_unchecked(raw);
    /// }
    /// ```
    #[must_use]
    pub unsafe fn from_mutf8_vec_unchecked(v: Vec<u8>) -> Self {
        // SAFETY: observing any of this data as an Mutf8CString should be benign within this function
        // we panic on debug mode for mutf8/nul-byte incompatibility
        // or assume that the caller has asserted both conditions in release
        let unchecked = unsafe { Self::_from_mutf8_vec_unchecked(v) };

        if cfg!(debug_assertions) {
            Mutf8CStr::from_bytes_with_nul(&unchecked.inner)
                .expect("bytes provided to from_vec_unchecked were not valid mutf-8");
        }

        // checked above only in debug mode
        unchecked
    }

    /// Converts a Vec<u8> to an Mutf8CString, adding on a nul-terminator.
    /// 
    /// # Safety
    /// The inner method does not validate against non-mutf8 data, namely interior or terminating nuls. 
    unsafe fn _from_mutf8_vec_unchecked(mut v: Vec<u8>) -> Self {
        v.reserve_exact(1);
        v.push(0);
        Self::_from_mutf8c_vec_with_nul_unchecked(v)
    }

    #[inline]
    unsafe fn _from_mutf8c_vec_with_nul_unchecked(v: Vec<u8>) -> Self {
        Self { inner: v.into_boxed_slice() }
    }

    /// Retakes ownership of a `Mutf8CString` that was transferred to C via
    /// [`Mutf8CString::into_raw`].
    ///
    /// Additionally, the length of the string will be recalculated from the pointer.
    ///
    /// # Safety
    ///
    /// This should only ever be called with a pointer that was earlier
    /// obtained by calling [`Mutf8CString::into_raw`]. Other usage (e.g., trying to take
    /// ownership of a string that was allocated by foreign code) is likely to lead
    /// to undefined behavior or allocator corruption.
    ///
    /// It should be noted that the length isn't just "recomputed," but that
    /// the recomputed length must match the original length from the
    /// [`Mutf8CString::into_raw`] call. This means the [`Mutf8CString::into_raw`]/`from_raw`
    /// methods should not be used when passing the string to C functions that can
    /// modify the string's length. The inner contract of the string being valid mutf8 must
    /// also be preserved.
    ///
    /// > **Note:** If you need to borrow a string that was allocated by
    /// > foreign code, use [`Mutf8CStr`]. If you need to take ownership of
    /// > a string that was allocated by foreign code, you will need to
    /// > make your own provisions for freeing it appropriately, likely
    /// > with the foreign code's API to do that.
    ///
    /// # Examples
    ///
    /// Creates a `Mutf8CString`, pass ownership to an `extern` function (via raw pointer), then retake
    /// ownership with `from_raw`:
    ///
    /// ```ignore (extern-declaration)
    /// use cesu8str::Mutf8CString;
    /// use std::os::raw::c_char;
    ///
    /// extern "C" {
    ///     fn some_extern_function(s: *mut c_char);
    /// }
    ///
    /// let mutf8c_string = Mutf8CString::new("Hello!").expect("Mutf8CString::new failed");
    /// let raw = mutf8c_string.into_raw();
    /// unsafe {
    ///     some_extern_function(raw);
    ///     let mutf8c_string = Mutf8CString::from_raw(raw);
    /// }
    /// ```
    #[must_use = "call `drop(from_raw(ptr))` if you intend to drop the `Mutf8CString`"]
    pub unsafe fn from_raw(ptr: *mut c_char) -> Mutf8CString {
        // SAFETY: This is called with a pointer that was obtained from a call
        // to `Mutf8CString::into_raw` and the length and data has not been modified. As such,
        // we know there is a NUL byte (and only one) at the end and that the
        // information about the size of the allocation is correct on Rust's
        // side.
        unsafe {
            extern "C" {
                /// Provided by libc or compiler_builtins.
                fn strlen(s: *const c_char) -> usize;
            }

            let len = strlen(ptr) + 1; // Including the NUL byte
            let slice = std::slice::from_raw_parts_mut(ptr, len);
            Mutf8CString { inner: Box::from_raw(slice as *mut [c_char] as *mut [u8]) }
        }
    }


    /// Consumes the `Mutf8CString` and transfers ownership of the string to a C caller.
    ///
    /// The pointer which this function returns must be returned to Rust and reconstituted using
    /// [`Mutf8CString::from_raw`] to be properly deallocated. Specifically, one
    /// should *not* use the standard C `free()` function to deallocate
    /// this string.
    ///
    /// Failure to call [`Mutf8CString::from_raw`] will lead to a memory leak.
    ///
    /// The C side must **not** modify the length of the string (by writing a
    /// `null` somewhere inside the string or removing the final one) before
    /// it makes it back into Rust using [`Mutf8CString::from_raw`]. See the safety section
    /// in [`Mutf8CString::from_raw`].
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    ///
    /// let mutf8c_string = Mutf8CString::new("foo").expect("Mutf8CString::new failed");
    ///
    /// let ptr = mutf8c_string.into_raw();
    ///
    /// unsafe {
    ///     assert_eq!(b'f', *ptr as u8);
    ///     assert_eq!(b'o', *ptr.add(1) as u8);
    ///     assert_eq!(b'o', *ptr.add(2) as u8);
    ///     assert_eq!(b'\0', *ptr.add(3) as u8);
    ///
    ///     // retake pointer to free memory
    ///     let _ = Mutf8CString::from_raw(ptr);
    /// }
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_raw(self) -> *mut c_char {
        Box::into_raw(self.into_inner()) as *mut c_char
    }

    /// Consumes the `Mutf8CString` and returns the underlying byte buffer.
    ///
    /// The returned buffer does **not** contain the trailing nul
    /// terminator, and it is guaranteed to not have any interior nul
    /// bytes and be in mutf8 encoding.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    ///
    /// let mutf8c_string = Mutf8CString::new("foo").expect("Mutf8CString::new failed");
    /// let bytes = mutf8c_string.into_bytes();
    /// assert_eq!(bytes, vec![b'f', b'o', b'o']);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_bytes(self) -> Vec<u8> {
        let mut vec = self.into_inner().into_vec();
        let _nul = vec.pop();
        debug_assert_eq!(_nul, Some(0u8));
        vec
    }

    /// Equivalent to [`Mutf8CString::into_bytes()`] except that the
    /// returned vector includes the trailing nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    ///
    /// let mutf8c_string = Mutf8CString::new("foo").expect("Mutf8CString::new failed");
    /// let bytes = mutf8c_string.into_bytes_with_nul();
    /// assert_eq!(bytes, vec![b'f', b'o', b'o', b'\0']);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_bytes_with_nul(self) -> Vec<u8> {
        self.into_inner().into_vec()
    }


    /// Returns the contents of this `Mutf8CString` as a slice of bytes.
    ///
    /// The returned slice does **not** contain the trailing nul
    /// terminator, and it is guaranteed to not have any interior nul
    /// bytes. If you need the nul terminator, use
    /// [`Mutf8CString::as_bytes_with_nul`] instead.
    /// 
    /// The returned slice is guaranteed to be in mutf8 encoding.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    ///
    /// let mutf8c_string = Mutf8CString::new("foo").expect("Mutf8CString::new failed");
    /// let bytes = mutf8c_string.as_bytes();
    /// assert_eq!(bytes, &[b'f', b'o', b'o']);
    /// ```
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY: Mutf8CString has a length at least 1
        unsafe { self.inner.get_unchecked(..self.inner.len() - 1) }
    }

    /// Equivalent to [`Mutf8CString::as_bytes()`] except that the
    /// returned slice includes the trailing nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    ///
    /// let mutf8c_string = Mutf8CString::new("foo").expect("Mutf8CString::new failed");
    /// let bytes = mutf8c_string.as_bytes_with_nul();
    /// assert_eq!(bytes, &[b'f', b'o', b'o', b'\0']);
    /// ```
    #[inline]
    #[must_use]
    pub fn as_bytes_with_nul(&self) -> &[u8] {
        &self.inner
    }

    /// Converts this `Mutf8CString` into a boxed [`CStr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::{CString, CStr};
    /// use cesu8str::Mutf8CString;
    ///
    /// let mutf8c_string = Mutf8CString::new(b"foo".to_vec()).expect("Mutf8CString::new failed");
    /// let boxed = mutf8c_string.into_boxed_mutf8c_str();
    /// assert_eq!(&*boxed,
    ///            CStr::from_bytes_with_nul(b"foo\0").expect("CStr::from_bytes_with_nul failed"));
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_boxed_mutf8c_str(self) -> Box<CStr> {
        unsafe { Box::from_raw(Box::into_raw(self.into_inner()) as *mut CStr) }
    }

    /// Converts this `Mutf8CString` into a boxed [`Mutf8CStr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::{Mutf8CString, Mutf8CStr};
    ///
    /// let mutf8c_string = Mutf8CString::new(b"foo".to_vec()).expect("Mutf8CString::new failed");
    /// let boxed = mutf8c_string.into_boxed_mutf8c_str();
    /// assert_eq!(&*boxed,
    ///            Mutf8CStr::from_bytes_with_nul(b"foo\0").expect("Mutf8CStr::from_bytes_with_nul failed"));
    /// ```
    pub fn into_boxed_mutf8_cstr(self) -> Box<Mutf8CStr> {
        unsafe { Box::from_raw(Box::into_raw(self.into_inner()) as *mut Mutf8CStr) }
    }

    /// Bypass "move out of struct which implements [`Drop`] trait" restriction.
    #[inline]
    fn into_inner(self) -> Box<[u8]> {
        // Rationale: `mem::forget(self)` invalidates the previous call to `ptr::read(&self.inner)`
        // so we use `ManuallyDrop` to ensure `self` is not dropped.
        // Then we can return the box directly without invalidating it.
        // See https://github.com/rust-lang/rust/issues/62553.
        let this = std::mem::ManuallyDrop::new(self);
        unsafe { std::ptr::read(&this.inner) }
    }

    /// Converts a <code>[Vec]<[u8]></code> to a [`Mutf8CString`] without checking the
    /// invariants on the given [`Vec`].
    ///
    /// # Safety
    ///
    /// The given [`Vec`] **must** have one nul byte as its last element.
    /// This means it cannot be empty nor have any other nul byte anywhere else.
    /// It must also consist of a valid mutf8-encoded string.
    ///
    /// # Example
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    /// assert_eq!(
    ///     unsafe { Mutf8CString::from_mutf8_vec_with_nul_unchecked(b"abc\0".to_vec()) },
    ///     unsafe { Mutf8CString::from_mutf8_vec_unchecked(b"abc".to_vec()) }
    /// );
    /// ```
    #[must_use]
    pub unsafe fn from_mutf8_vec_with_nul_unchecked(v: Vec<u8>) -> Self {
        if cfg!(debug_assertions) {
            // checks string not empty
            // checks last byte is nul
            // checks mutf8 and no interior nuls            
            if let Err(e) = Mutf8CStr::from_bytes_with_nul(&v) {
                panic!("expected valid nul-terminated mutf8: {:?}", e);
            }
        }

        unsafe { Self::_from_mutf8c_vec_with_nul_unchecked(v) }
    }



    /// Attempts to converts a <code>[Vec]<[u8]></code> to a [`Mutf8CString`].
    ///
    /// Runtime checks are present to ensure there is only one nul byte in the
    /// [`Vec`], its last element, and also ensure mutf8 encoding.
    ///
    /// # Errors
    ///
    /// If the string is not mutf8, a nul byte is present and not the last element or no nul bytes
    /// is present, an error will be returned.
    ///
    /// # Examples
    ///
    /// A successful conversion will produce the same result as [`Mutf8CString::new`]
    /// when called without the ending nul byte.
    ///
    /// ```
    /// use cesu8str::Mutf8CString;
    /// assert_eq!(
    ///     Mutf8CString::from_mutf8_vec_with_nul(b"abc\0".to_vec())
    ///         .expect("Mutf8CString::from_mutf8_vec_with_nul failed"),
    ///     Mutf8CString::new(b"abc".to_vec()).expect("Mutf8CString::new failed")
    /// );
    /// ```
    ///
    /// An incorrectly formatted [`Vec`] will produce an error.
    ///
    /// ```
    /// use cesu8str::{Mutf8CString, FromMutf8BytesWithNulError};
    /// // Interior nul byte
    /// let _: FromMutf8BytesWithNulError = Mutf8CString::from_mutf8_vec_with_nul(b"a\0bc".to_vec()).unwrap_err();
    /// // No nul byte
    /// let _: FromMutf8BytesWithNulError = Mutf8CString::from_mutf8_vec_with_nul(b"abc".to_vec()).unwrap_err();
    /// ```
    pub fn from_mutf8_vec_with_nul(v: Vec<u8>) -> Result<Self, FromMutf8BytesWithNulError> {
        match Mutf8CStr::from_bytes_with_nul(&v) {
            Ok(_) => Ok(unsafe {
                // SAFETY: We've checked for a nul terminator and mutf8 encoding
                Mutf8CString::_from_mutf8c_vec_with_nul_unchecked(v)
            }),
            Err(err) => Err(FromMutf8BytesWithNulError {
                kind: err,
                bytes: v,
            })
        }
    }

    /// Converts a <code>[Box]<[CStr]></code> into a [`Mutf8CString`] without copying or allocating
    #[inline]
    pub fn from_boxed_mutf8c(v: Box<Mutf8CStr>) -> Mutf8CString {
        let raw = Box::into_raw(v) as *mut [u8];
        // Safety: our internal raw box is correct, because we just retrieved it from a valid box
        Mutf8CString { inner: unsafe { Box::from_raw(raw) } }
    }
}

impl Mutf8CStr {
    /// Converts a `&str` to a `Mutf8CStr`
    /// 
    /// Requires a nul-terminator, that is the only nul byte in the [`&str`]. If other nul-bytes exist
    /// 
    /// Allocates only if the UTF-8 string contains inner nul-bytes (that must be re-encoded) or has 4-byte UTF-8
    /// sequences (that must be re-encoded).
    /// 
    /// This string must contain a nul-byte at the end, or it will return an Err(_)
    pub fn from_str_nul_terminated(s: &str) -> Result<Cow<'_, Mutf8CStr>, FromStrWithNulError> {
        
        // cannot panic on split - we're splitting off the last character:
        // * we've determined it is a 1-byte char nul terminator
        // * the rest of the string is valid UTF-8, so no partial codepoints
        // let rest = s.split_at(s.len() - 1).0;

        // check for nul byte being last
        // explicitly not checking for interior nuls:
        if !s.ends_with('\0') {
            return Err(FromStrWithNulError { string: s.to_owned() });
        };

        let rest = s.split_at(s.len()-1).0;

        let mutf8 = crate::Cesu8Str::from_utf8(rest, Variant::Java);

        // the string should only be Cow::Owned
        match mutf8.bytes {
            Cow::Borrowed(ms) => {
                debug_assert_eq!(ms, s.as_bytes(), "borrowed Mutf8 data not the same as source UTF-8 data");

                // SAFETY: We've validated the non-terminated portion to be MUTF-8 with Cesu8Str::from_utf8
                // we've also ensured there is a nul-terminator directly after the string bytes
                Ok(Cow::Borrowed(unsafe {
                    Self::from_bytes_with_nul_unchecked(s.as_bytes())
                }))
            },
            Cow::Owned(mut ms) => {
                // add nul-byte to allocation if re-encoded (we previously stripped nul-byte)
                ms.push(b'\0');

                // SAFETY: We've validated the non-terminated portion to be MUTF-8 with Cesu8Str::from_utf8
                // and we've re-applied the nul-terminator to the new allocation above
                Ok(Cow::Owned(unsafe { Mutf8CString::_from_mutf8c_vec_with_nul_unchecked(ms) }))
            },
        }
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
        unsafe { Mutf8CStr::from_bytes_with_nul_unchecked(self.as_bytes_with_nul()) }
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
