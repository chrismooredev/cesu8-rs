
use std::borrow::Cow;
use std::str;
use std::fmt;
use std::ffi::c_char;
use std::hash::Hash;


// Cesu8Str
// Cesu8String
// Cesu8CStr
// Cesu8CString
// Mutf8CStr
// Mutf8CString

use std::ffi::CStr;

use crate::Cesu8Str;
use crate::Mutf8CString;

use super::NGCesu8CError;

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

// custom impls
impl Mutf8CStr {
    /// Uses pointer magic to transmute a byte slice to an instance of Mutf8CStr
    /// 
    /// # Safety
    /// The CStr should be encoded in nul-terminated MUTF8. That is, UTF8 with 4-byte-sequences re-encoded as 2, 3-byte sequences,
    /// and with nul bytes re-encoded as as [0xC0, 0x80]
    unsafe fn _from_bytes_with_nul_unchecked(bytes: &[u8]) -> &Mutf8CStr {
        // &[u8]
        // *const [u8]
        // *const Mutf8Str
        // &Mutf8Str

        // should be a no-op

        &*(bytes as *const [u8] as *const Mutf8CStr)
    }

    /// Uses pointer magic to transmute an instance of CStr to an instance of Mutf8CStr
    /// 
    /// # Safety
    /// The CStr should be encoded in MUTF8. That is, UTF8 with 4-byte-sequences re-encoded as 2, 3-byte sequences,
    /// and with nul bytes re-encoded as as [0xC0, 0x80]
    const unsafe fn _from_mutf8_cstr_unchecked(cs: &CStr) -> &Mutf8CStr {
        // &CStr
        // *const CStr
        // *const [u8]
        // *const Mutf8Str
        // &Mutf8Str

        // should be a no-op

        &*(cs as *const CStr as *const [u8] as *const Mutf8CStr)
    }

    /// Uses pointer magic to transmute an instance of Mutf8CStr to an instance of CStr
    const fn _into_mutf8_cstr_unchecked(&self) -> &CStr {
        // &Mutf8CStr
        // *const Mutf8CStr
        // *const [u8]
        // *const CStr
        // &CStr

        // should be a no-op

        unsafe { 
            &*(self as *const Mutf8CStr as *const [u8] as *const CStr)
        }
    }

    /// Uses pointer magic to transmute an instance of CStr to an instance of Mutf8CStr
    /// 
    /// # Safety
    /// The CStr should be encoded in MUTF8. That is, UTF8 with 4-byte-sequences re-encoded as 2, 3-byte sequences,
    /// and with nul bytes re-encoded as as [0xC0, 0x80]
    unsafe fn from_cstr_unchecked(cs: &CStr) -> &Mutf8CStr {
        if cfg!(debug_assertions) {
            // always validate cesu8 as mutf8/encoded nuls => cannot have nul bytes within a CStr
            match crate::decoding::cesu8_validate::<true>(cs.to_bytes()) {
                Ok(_) => {
                    // good cesu8, possibly bad utf8
                },
                Err(e) => {
                    let preview = std::string::String::from_utf8_lossy(cs.to_bytes());
                    panic!(concat!(
                        "attempted to create an Mutf8CStr from a non-Mutf8 c string with from_ptr!",
                        " (ptr = {:p}, orig_str_preview = {:?}, error = {:?})"),
                        cs.as_ptr(), preview, e
                    );
                }
            }
        }

        Self::_from_mutf8_cstr_unchecked(cs)
    }

    /// Converts a `Mutf8CStr` to a <code>[Cow]<[prim@str]></code>. The returned string will not contain a nul-terminator.
    /// 
    /// Allocates if the contained MUTF-8 is not valid UTF-8:
    /// * Contains encoded nul bytes
    /// * Contains 4-byte UTF-8 sequences encoded as 3-byte surrogate pairs
    pub fn to_string(&self) -> Cow<str> {
        let bytes = self.to_bytes();
        let cesu = Cesu8Str::from_cesu8(bytes, crate::Variant::Java).expect("found invalid CESU8 within Mutf8CStr");
        match cesu.utf8_error {
            Ok(()) => Cow::Borrowed(crate::decoding::from_utf8_slice(
                bytes,
                "utf8_err was not updated/set correctly",
            )),
            Err(_) => Cow::Owned(crate::decoding::cesu8_to_utf8(&cesu)),
        }
    }



    /// Extracts a [`CStr`] slice containing the entire string.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::{CString, CStr};
    ///
    /// let c_string = CString::new(b"foo".to_vec()).expect("CString::new failed");
    /// let cstr = c_string.as_c_str();
    /// assert_eq!(cstr,
    ///            CStr::from_bytes_with_nul(b"foo\0").expect("CStr::from_bytes_with_nul failed"));
    /// ```
    pub fn as_c_str(&self) -> &CStr {
        self._into_mutf8_cstr_unchecked()
    }

    /// The length of the MUTF8 string in bytes, excluding the terminating nul byte.
    pub fn len(&self) -> usize {
        self.inner.len() - 1
    }

    /// The length of the MUTF8 string in bytes, including the terminating nul byte.
    pub fn len_with_nul(&self) -> usize {
        self.inner.len()
    }

    /// Creates an Mutf8CStr that may nor may not allocate. Must be terminated by a singular nul byte. No other nul
    /// bytes may exist in the string. Will only allocate if 4-byte utf8 sequences exist.
    /// 
    /// # Panics
    /// Panics if the string is not terminated with a nul-byte, or contains nul bytes outside the last character.
    #[inline]
    pub fn from_utf8_with_nul(s: &str) -> Cow<Mutf8CStr> {
        let data: &[u8] = match s.as_bytes() {
            [rest @ .., b'\0'] => rest,

            // either zero-length or no ending nul byte
            [..] => panic!("string passed to Mutf8CStr::from_utf8_with_nul is not nul terminated: {s:?}"),
        };

        let data_utf8 = &s[..s.len()-1];
        let utf8_as_cesu8 = crate::encoding::utf8_as_cesu8_spec::<true>(&data_utf8);
        let mutf8 = match utf8_as_cesu8 {
            // Safety: validated that all bytes (except nul-terminator) are valid CESU8, while also being UTF8
            // so pass the string as bytes, including the required nul-terminator
            Ok(()) => Cow::Borrowed(unsafe { Mutf8CStr::_from_bytes_with_nul_unchecked(s.as_bytes()) }),
            Err(e) => {
                if s.len() >= e.valid_up_to && s.as_bytes()[e.valid_up_to] == b'\0' {
                    panic!("string passed to Mutf8CStr::from_utf8_with_nul contained an interior nul: {s:?}");
                }

                // Safety: We've pre-checked that `data_utf8[..e.valid_up_to]` is valid CESU-8, continue from there,
                // reencoding as necessary
                Cow::Owned(unsafe {
                    let mut v = Vec::with_capacity(crate::default_cesu8_capacity(s.len()));
                    let _utf8_err = crate::encoding::utf8_to_cesu8_spec::<_, true>(data_utf8, e.valid_up_to, &mut v).unwrap();
                    v.push(b'\0'); // add back the nul-byte
                    Mutf8CString::from_mutf8_vec_unchecked(v)
                })
            }
        };
        
        mutf8
    }
}

// heavily adjusted copies from std::ffi::CStr
impl Mutf8CStr {
    /// Wraps a raw C string with a safe C mutf8 encoded wrapper.
    /// 
    /// # Safety
    /// * The memory pointed to by `ptr` must contain a valid nul terminator at the end of the string.
    /// * `ptr` must be [valid] for reads of bytes up to and including the null terminator.
    ///   In particular:
    ///     * The entire memory range of this `Mutf8Cstr` must be contained within a single allocated object
    ///     * `ptr` must be non-null even for a zero-length mutf8 string
    /// * The memory referenced by the returned `Mutf8CStr` must not be mutated for the duration of lifetime `'a`.
    /// * The size of the string is at most `isize::MAX`
    /// 
    /// Note the following additions to the traditional `CStr` type:
    /// * The memory pointed to be `ptr` must be valid Modified UTF-8.
    /// In comparison to UTF-8:
    ///    * nul bytes (`'\0'`) are converted to the null byte sequence (`[0xC0, 0x80]`)
    ///    * four-byte codepoints are converted into the appropriate surrogate pairs
    /// 
    /// # Caveat
    ///
    /// The lifetime for the returned slice is inferred from its usage. To prevent accidental misuse,
    /// it's suggested to tie the lifetime to whichever source lifetime is safe in the context,
    /// such as by providing a helper function taking the lifetime of a host value for the slice,
    /// or by explicit annotation.
    /// 
    /// [valid]: core::ptr#safety
    pub unsafe fn from_ptr<'a>(ptr: *const c_char) -> &'a Self {
        let cs = CStr::from_ptr(ptr);

        // SAFETY: Caller guarantees that needed by CStr/our own encoding
        // and transmute_from_str will also validate in debug mode
        Self::from_cstr_unchecked(cs)
    }

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
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&Self, NGCesu8CError> {
        // quick-path if empty or not nul-terminated
        let data: &[u8] = match bytes {
            [rest @ .., b'\0'] => Ok(rest),

            // either zero-length or no ending nul byte
            [..] => Err(NGCesu8CError::NotNulTerminated),
        }?;
        
        match crate::decoding::cesu8_validate::<true>(data) {
            Ok(_) => {
                // SAFETY: We know it is a valid string. The encoding validates no interior nuls, and the previous
                // check ensures the last byte is a nul terminator. we've also validated for MUTF8
                Ok(unsafe { Mutf8CStr::_from_bytes_with_nul_unchecked(bytes) })
            },
            Err(e) => {
                Err(NGCesu8CError::Encoding(e))
            }
        }
    }

    /// Unsafely creates an MUTF-8 C string wrapper from a byte slice.
    ///
    /// This function will cast the provided `bytes` to a `Mutf8CStr` wrapper without
    /// performing any sanity checks.
    ///
    /// # Safety
    /// The provided slice **must** be nul-terminated and not contain any interior
    /// nul bytes while being encoded as mutf8.
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::{Mutf8CStr, Mutf8CString};
    ///
    /// unsafe {
    ///     let mutf8cstring = Mutf8CString::new("hello").expect("Mutf8CString::new failed");
    ///     let mutf8cstr = Mutf8CStr::from_bytes_with_nul_unchecked(mutf8cstring.to_bytes_with_nul());
    ///     assert_eq!(mutf8cstr, &*mutf8cstring);
    /// }
    /// ```
    pub unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> &Mutf8CStr {
        if cfg!(debug_assertions) {
            if let Err(e) = Self::from_bytes_with_nul(bytes) {
                panic!("bad string passed to from_bytes_with_nul_unchecked: {:?}", e);
            }
        }
        
        Mutf8CStr::_from_bytes_with_nul_unchecked(bytes)
    }
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

    /// Yields a <code>&[str]</code> slice if the `Mutf8CStr` contains valid UTF-8.
    ///
    /// If the contents of the `Mutf8CStr` are valid UTF-8 data, this
    /// function will return the corresponding <code>&[str]</code> slice. Otherwise,
    /// it will return an error with details of where UTF-8 validation failed.
    ///
    /// [str]: prim@str "str"
    ///
    /// # Examples
    ///
    /// ```
    /// use cesu8str::Mutf8CStr;
    ///
    /// let mutf8str = Mutf8CStr::from_bytes_with_nul(b"foo\0").expect("Mutf8CStr::from_bytes_with_nul failed");
    /// assert_eq!(mutf8str.to_str(), Ok("foo"));
    /// ```
    pub fn to_str(&self) -> Result<&str, str::Utf8Error> {
        // N.B., when `CStr` is changed to perform the length check in `.to_bytes()`
        // instead of in `from_ptr()`, it may be worth considering if this should
        // be rewritten to do the UTF-8 check inline with the length calculation
        // instead of doing it afterwards.
        str::from_utf8(self.to_bytes())
    }
}
impl fmt::Debug for Mutf8CStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: turn this into a more iterator-focused view, possibly stack allocate
        let rs_str = self.to_string();
        write!(f, "{:?}", &rs_str)
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
        // TODO: turn this into a more iterator-focused view, possibly stack allocate
        let rs_str = self.to_string();
        write!(f, "{}", &rs_str)
    }
}
impl Hash for Mutf8CStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // TODO: turn this into a more iterator-focused view, possibly stack allocate
        self.to_string().hash(state);
    }
}

