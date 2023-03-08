
use std::ops::Deref;
use std::fmt;
use std::ffi::c_char;
use std::hash::Hash;
use std::ffi::CStr;

use crate::Mutf8Str;

use super::BaseCesu8StrEncoding;
use super::Cesu8CStrEncoding;

/// An error indicating that nul byte was not in the expected position
/// 
/// The `str` used to create a `Mutf8CStr` did not have a nul byte, positioned at the end.
/// 
/// This error is created by the `Mutf8CStr::from_str_nul_terminated` method. See its documentation for more.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FromStrWithNulError {
    pub(crate) string: String,
}

/// A nul-terminated Modified UTF-8 string, valid for use with JNI


/// Representation of a borrowed Mutf8 C string.
///
/// This type represents a borrowed reference to a nul-terminated
/// array of bytes. It can be constructed safely from a <code>&[[u8]]</code>
/// slice, or unsafely from a raw `*const c_char`. It can then be
/// converted to a Rust <code>&[str]</code> by performing UTF-8 validation, or
/// into an owned [`String`]/[`CString`]/[`Mutf8CString`].
///
/// `&Mutf8CStr` is to [`Mutf8CString`] as <code>&[str]</code> is to [`String`]: the former
/// in each pair are borrowed references; the latter are owned
/// strings.
///
/// Note that this structure is **not** `repr(C)` and is not recommended to be
/// placed in the signatures of FFI functions. Instead, safe wrappers of FFI
/// functions may leverage the unsafe [`Mutf8CStr::from_ptr`] constructor to provide
/// a safe interface to other consumers.
///
/// [`CString`]: ::std::ffi::CString
/// [`String`]: ::std::string::String
///
/// # Examples
///
/// Inspecting a foreign C string:
///
/// ```ignore (extern-declaration)
/// use std::ffi::CStr;
/// use std::os::raw::c_char;
///
/// extern "C" { fn my_jni_string() -> *const c_char; }
///
/// unsafe {
///     let slice = Mutf8CStr::from_ptr(my_string());
///     println!("string buffer size without nul terminator: {}", slice.to_bytes().len());
/// }
/// ```
///
/// Passing a Rust-originating C string:
///
/// ```ignore (extern-declaration)
/// use std::ffi::{CString, CStr};
/// use std::os::raw::c_char;
///
/// fn work(data: &Mutf8CStr) {
///     extern "C" { fn work_with(data: *const c_char); }
///
///     unsafe { work_with(data.as_ptr()) }
/// }
///
/// let s = Mutf8CString::new("data data data data").expect("CString::new failed");
/// work(&s);
/// ```
///
/// Converting a foreign C string into a Rust `String`:
///
/// ```ignore (extern-declaration)
/// use std::ffi::CStr;
/// use std::os::raw::c_char;
///
/// extern "C" { fn my_jni_string() -> *const c_char; }
///
/// fn my_string_safe() -> String {
///     let cstr = unsafe { Mutf8CStr::from_ptr(my_string()) };
///     // Get copy-on-write Cow<'_, str>, then guarantee a freshly-owned String allocation
///     Mutf8CString::from_utf8_lossy(cstr.to_bytes()).to_string()
/// }
///
/// println!("string: {}", my_string_safe());
/// ```
///
/// [str]: prim@str "str"
#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Mutf8CStr {
    // FIXME: This implementation is based off stdlib's CStr which as of writing uses a DST slice
    // however it has a 'FIXME' tag saying it should go to a raw c_char with an unsized type marker.
    //
    // As we're using CStr as a reference... If a DST slice is good enough for stdlib, it's good enough here.
    // we can consider moving this over when they do.
    inner: [u8],
}
impl BaseCesu8StrEncoding for Mutf8CStr {
    const ENCODE_NUL: bool = true;
    const NUL_TERM: bool = true;

    /// Uses pointer magic to transmute a byte slice to an instance of Mutf8CStr
    /// 
    /// # Safety
    /// The CStr should be encoded in nul-terminated MUTF8. That is, UTF8 with 4-byte-sequences re-encoded as 2, 3-byte sequences,
    /// and with nul bytes re-encoded as as [0xC0, 0x80]
    unsafe fn _from_bytes_unchecked(bytes: &[u8]) -> &Self {
        // &[u8]
        // *const [u8]
        // *const Mutf8Str
        // &Mutf8Str

        // should be a no-op
        &*(bytes as *const [u8] as *const Self)
    }

    fn _raw_bytes(&self) -> &[u8] {
        unsafe { 
            &*(self as *const Self as *const [u8])
        }
    }
}
impl Cesu8CStrEncoding for Mutf8CStr {
    
}

// heavily adjusted copies from std::ffi::CStr
impl Mutf8CStr {

    /// Creates an MUTF-8 C string wrapper from a byte slice.
    ///
    /// This function will cast the provided `bytes` to a `Mutf8CStr`
    /// wrapper after ensuring that the byte slice is nul-terminated
    /// and does not contain any interior nul bytes. This also checks
    /// for mutf-8 compliance.
    ///
    /// If the nul byte may not be at the end,
    /// [`Mutf8CStr::from_bytes_until_nul`] can be used instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CStr;
    ///
    /// let mutf8cstr = Mutf8CStr::from_bytes_with_nul(b"hello\0");
    /// assert!(mutf8cstr.is_ok());
    /// ```
    ///
    /// Creating a `Mutf8CStr` without a trailing nul terminator is an error:
    ///
    /// ```
    /// use cesu8str::Mutf8CStr;
    ///
    /// let mutf8cstr = Mutf8CStr::from_bytes_with_nul(b"hello");
    /// assert!(mutf8cstr.is_err());
    /// ```
    ///
    /// Creating a `CStr` with an interior nul byte is an error:
    ///
    /// ```
    /// use cesu8str::Mutf8CStr;
    ///
    /// let mutf8cstr = Mutf8CStr::from_bytes_with_nul(b"he\0llo\0");
    /// assert!(mutf8cstr.is_err());
    /// ```
    pub fn _placeholder0() {}

}

// mostly copied from std::ffi::CStr
impl Mutf8CStr {



    /// Returns the inner pointer to this MUTF-8 C string.
    ///
    /// The returned pointer will be valid for as long as `self` is, and points
    /// to a contiguous region of memory terminated with a 0 byte to represent
    /// the end of the string.
    ///
    /// **WARNING**
    ///
    /// The returned pointer is read-only; writing to it (including passing it
    /// to C code that writes to it) causes undefined behavior.
    ///
    /// It is your responsibility to make sure that the underlying memory is not
    /// freed too early. For example, the following code will cause undefined
    /// behavior when `ptr` is used inside the `unsafe` block:
    ///
    /// ```no_run
    /// # #![allow(unused_must_use)] #![allow(temporary_cstring_as_ptr)]
    /// use cesu8str::Mutf8CString;
    ///
    /// let ptr = Mutf8CString::new("Hello").expect("Mutf8CString::new failed").as_ptr();
    /// unsafe {
    ///     // `ptr` is dangling
    ///     *ptr;
    /// }
    /// ```
    ///
    /// This happens because the pointer returned by `as_ptr` does not carry any
    /// lifetime information and the `Mutf8CString` is deallocated immediately after
    /// the `Mutf8CString::new("Hello").expect("Mutf8CString::new failed").as_ptr()`
    /// expression is evaluated.
    /// To fix the problem, bind the `Mutf8CString` to a local variable:
    ///
    /// ```no_run
    /// # #![allow(unused_must_use)]
    /// use cesu8str::Mutf8CString;
    ///
    /// let hello = Mutf8CString::new("Hello").expect("Mutf8CString::new failed");
    /// let ptr = hello.as_ptr();
    /// unsafe {
    ///     // `ptr` is valid because `hello` is in scope
    ///     *ptr;
    /// }
    /// ```
    ///
    /// This way, the lifetime of the `Mutf8CString` in `hello` encompasses
    /// the lifetime of `ptr` and the `unsafe` block.
    pub const fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr() as *const c_char
    }

    /// Returns `true` if `self.to_bytes()` has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CStr;
    /// # use cesu8str::NGCesu8CError;
    ///
    /// # fn main() { test().unwrap(); }
    /// # fn test() -> Result<(), NGCesu8CError> {
    /// let mutf8str = Mutf8CStr::from_bytes_with_nul(b"foo\0")?;
    /// assert!(!mutf8str.is_empty());
    ///
    /// let empty_mutf8str = Mutf8CStr::from_bytes_with_nul(b"\0")?;
    /// assert!(empty_mutf8str.is_empty());
    /// # Ok(())
    /// # }
    /// ```
    pub fn is_empty(&self) -> bool {
        debug_assert_eq!(self.inner.last(), Some(&b'\0'), "Mutf8CStr does not have a nul-terminator");
        // SAFETY: We know there is at least one byte; for empty strings it
        // is the NUL terminator.
        (unsafe { self.inner.get_unchecked(0) }) == &b'\0'
    }

    /// Converts this MUTF-8 C string to a byte slice.
    ///
    /// The returned slice will **not** contain the trailing nul terminator that this MUTF-8 C
    /// string has.
    ///
    /// > **Note**: This method is currently implemented as a constant-time
    /// > cast, but it is planned to alter its definition in the future to
    /// > perform the length calculation whenever this method is called.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CStr;
    ///
    /// let mutf8str = Mutf8CStr::from_bytes_with_nul(b"foo\0").expect("Mutf8CStr::from_bytes_with_nul failed");
    /// assert_eq!(mutf8str.to_bytes(), b"foo");
    /// ```
    pub fn to_bytes(&self) -> &[u8] {
        debug_assert_eq!(self.inner.last(), Some(&b'\0'), "Mutf8CStr does not have a nul-terminator");
        let bytes = self.to_bytes_with_nul();
        // SAFETY: to_bytes_with_nul returns slice with length at least 1
        unsafe { bytes.get_unchecked(..bytes.len() - 1) }
    }

    /// Converts this MUTF-8 C string to a byte slice containing the trailing 0 byte.
    ///
    /// This function is the equivalent of [`Mutf8CStr::to_bytes`] except that it
    /// will retain the trailing nul terminator instead of chopping it off.
    ///
    /// > **Note**: This method is currently implemented as a 0-cost cast, but
    /// > it is planned to alter its definition in the future to perform the
    /// > length calculation whenever this method is called.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CStr;
    ///
    /// let mutf8str = Mutf8CStr::from_bytes_with_nul(b"foo\0").expect("Mutf8CStr::from_bytes_with_nul failed");
    /// assert_eq!(mutf8str.to_bytes_with_nul(), b"foo\0");
    /// ```
    pub const fn to_bytes_with_nul(&self) -> &[u8] {
        // SAFETY: Transmuting a slice of `c_char`s to a slice of `u8`s
        // is safe on all supported targets.
        unsafe { &*(&self.inner as *const [u8]) }
    }
}

impl fmt::Debug for Mutf8CStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &self.to_str())
    }
}
impl Default for &Mutf8CStr {
    fn default() -> Self {
        const SLICE: &[c_char] = &[0];
        // SAFETY: `SLICE` is indeed pointing to a valid nul-terminated string.
        unsafe { Mutf8CStr::from_ptr(SLICE.as_ptr()) }
    }
}
impl fmt::Display for Mutf8CStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_str())
    }
}
impl Hash for Mutf8CStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.to_str().hash(state);
    }
}
impl Deref for Mutf8CStr {
    type Target = Mutf8Str;
    fn deref(&self) -> &Self::Target {
        unsafe { Mutf8Str::_from_bytes_unchecked(self.as_bytes()) }
    }
}
