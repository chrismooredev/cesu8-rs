
use std::ops::Deref;
use std::ffi::c_char;
use std::ffi::CStr;

use super::prelude::*;


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

impl Mutf8CStr {
    super::impl_str_encoding_meths!(base);
    super::impl_str_encoding_meths!(cstr);
}

impl Mutf8CStr {
    /// Determines if this string encoding uses literal nul bytes. If true, then literal nul bytes are not allowed
    /// within the string's contents.
    pub const ENCODE_NUL: bool = true;
    /// Determines if this string maintains a literal nul byte as a terminator. This makes it functionally equilavent
    /// to a [`CStr`], including any encoding guarantees provided by the string type.
    /// 
    /// If this is `true`, then [`Self::ENCODE_NUL`] must also be `true`.
    pub const NUL_TERM: bool = true;

    /// Uses pointer magic to transmute a byte slice to an instance of Mutf8CStr
    /// 
    /// # Safety
    /// The CStr should be encoded in nul-terminated MUTF8. That is, UTF8 with 4-byte-sequences re-encoded as 2, 3-byte sequences,
    /// and with nul bytes re-encoded as as [0xC0, 0x80]
    pub(crate) const unsafe fn _from_bytes_unchecked(bytes: &[u8]) -> &Self {
        // &[u8]
        // *const [u8]
        // *const Mutf8Str
        // &Mutf8Str

        // should be a no-op
        &*(bytes as *const [u8] as *const Self)
    }

    pub(crate) const fn _raw_bytes(&self) -> &[u8] {
        unsafe { 
            &*(self as *const Self as *const [u8])
        }
    }
}

impl Default for &Mutf8CStr {
    fn default() -> Self {
        const SLICE: &[c_char] = &[0];
        // SAFETY: `SLICE` is indeed pointing to a valid nul-terminated string.
        unsafe { Mutf8CStr::from_ptr(SLICE.as_ptr()) }
    }
}
impl Deref for Mutf8CStr {
    type Target = Mutf8Str;
    fn deref(&self) -> &Self::Target {
        unsafe { Mutf8Str::_from_bytes_unchecked(self.as_bytes()) }
    }
}
impl ToOwned for Mutf8CStr {
    type Owned = Mutf8CString;
    fn to_owned(&self) -> Self::Owned {
        // SAFETY: Mutf8CStr uses the same invariants as Mutf8CString
        unsafe { Mutf8CString::_from_bytes_unchecked(self.as_bytes_with_nul().to_vec()) }
    }
}
