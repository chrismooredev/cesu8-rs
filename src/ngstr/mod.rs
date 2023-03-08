
// keep four string variants of actual types --
// null_terminated * ref/owned

// use an enum to internally switch between them, and only expose methods that statically
// switch methods - effectively optimizing out the runtime checks for the specific variant

use std::borrow::Cow;
use std::ffi::{c_char, CStr, CString};
use std::ops::Deref;

use self::prims::EncodingError;

/// An error type for creating a Cesu8/Mutf8 CStr/CString
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum NGCesu8CError {
    /// An interior nul byte was found within a CString. The contained usize is the index into the str/byte buffer.
    InteriorNul(usize),
    /// A function expected a buffer with a nul terminator, but could not find one
    NotNulTerminated,
    /// Encoding/Decoding error between UTF8, or CESU8
    Encoding(EncodingError),
}
impl From<EncodingError> for NGCesu8CError {
    fn from(value: EncodingError) -> Self {
        Self::Encoding(value)
    }
}



macro_rules! impl_from_with_nul {
    ($e: ident) => {
        #[derive(Debug, PartialEq, Eq, Clone)]
        pub struct $e {
            kind: NGCesu8CError,
            bytes: Vec<u8>,
        }
    }
}

impl_from_with_nul!(FromBytesWithNulError);
impl_from_with_nul!(FromUtf8WithNulError);


pub(crate) mod prims;
pub(crate) mod mutf8str;
pub(crate) mod mutf8string;
pub(crate) mod mutf8cstr;
pub(crate) mod mutf8cstring;
mod cross_impls;
pub use mutf8str::Mutf8Str;
pub use mutf8string::Mutf8String;
pub use mutf8cstr::Mutf8CStr;
pub use mutf8cstring::Mutf8CString;

// trait bounds used as a sort of compile time lint, to ensure they are all implemented
// trait bounds inspired by stdlib str/String

// trait StrEncoding:
//     fmt::Debug + fmt::Display + Hash
//     // + for<'a> From<&'a str>
//     // + for<'a> PartialEq<&'a str>
//     // + PartialEq<str>
//     // + PartialEq<Self>
// {
//     type FromBytesErr;
//     const encodes_nul: bool;
//     const nul_terminated: bool;

//     /// Takes a slice of bytes and converts it to this type.
//     unsafe fn from_bytes_unchecked(b: &[u8]) -> &Self;
//     // fn from_bytes(b: &[u8]) -> Result<&Self, EncodingError>;
//     fn as_bytes(&self) -> &[u8];

//     /// Attempts to cast a utf8 string to this type. If not possible, returns the index of the encoding incompatibility.
//     fn from_utf8(s: &str) -> Result<&Self, usize>;

//     /// A convience function for [`std::str::from_utf8`]
//     fn to_str(&self) -> Result<&str, Utf8Error> {
//         std::str::from_utf8(self.as_bytes())
//     }
//     fn to_string(&self) -> Cow<str>;
//     fn len(&self) -> usize {
//         self.as_bytes().len()
//     }
//     fn is_empty(&self) -> bool {
//         self.as_bytes().is_empty()
//     }
//     fn as_ptr(&self) -> *const c_char {
//         self.as_bytes().as_ptr() as *const c_char
//     }
// }
// trait StringEncoding:
//     Sized + Deref + Default
// where
//     <Self as Deref>::Target: StrEncoding
// {
//     type FromBytesErr;

//     unsafe fn from_bytes_unchecked(b: Vec<u8>) -> Self;
//     fn into_string(self) -> String;
//     fn into_raw(self) -> *mut c_char;
//     fn into_boxed(self) -> Box<Self::Target>;

//     fn capacity(&self) -> usize;
//     fn clear(&mut self);
    
//     fn from_utf8(s: String) -> Self;
//     fn from_bytes(b: Vec<u8>) -> Result<Self, EncodingError>;

//     // fn insert(&mut self, idx: usize, ch: char);
//     // fn insert_str(&mut self, idx: usize, string: &Self::Target);
//     // fn insert_utf8_str(&mut self, idx: usize, string: &str); 
//     fn into_bytes(self) -> Vec<u8>;
//     fn new() -> Self;
//     // fn pop(&mut self) -> Option<char>;
//     // fn push(&mut self, ch: char);
//     // fn push_str(&mut self, string: &Self::Target);
//     // fn push_utf8(&mut self, string: &str);
//     // fn remove(&mut self, idx: usize) -> char;
//     // fn replace_range<R: RangeBounds<usize>>(&mut self, range: R, replace_with: &Self::Target);
//     // fn reserve(&mut self, additional: usize);

//     // fn reserve_exact(&mut self, additional: usize);
//     // fn retain<F: FnMut(char) -> bool>(&mut self, f: F);
//     // fn shrink_to(&mut self, min_capacity: usize);
//     // fn shrink_to_fit(&mut self);
//     // fn truncate(&mut self, new_line: usize);
//     fn with_capacity(capacity: usize) -> Self;
// }


// #[derive(Debug, PartialEq, Eq, Clone, Copy)]
// enum StrEncoderMeta {
//     InteriorNuls,
//     EncodedNuls,
//     EncodedNulsWithNulTerminator,
// }
// impl StrEncoderMeta {
//     fn encodes_nuls(&self) -> bool {
//         ! matches!(self, Self::InteriorNuls)
//     }
//     fn nul_terminated(&self) -> bool {
//         matches!(self, Self::EncodedNulsWithNulTerminator)
//     }
// }

// #[derive(Debug, PartialEq, Eq, Clone, Copy)]
// enum StrAllocType {
//     Borrowed,
//     Owned,
// }

// #[derive(Debug, PartialEq, Eq, Clone, Copy)]
// struct StringEncodingMeta {
//     meta: StrEncoderMeta,
//     alloc_type: StrAllocType,
// }

// trait StrEncodingTmp {
//     const ENCODE_NUL: bool;
//     const NUL_TERMINATED: bool;
//     //  where [u8; {ENCODE_NUL as usize - 1}]: ;

//     fn as_bytes(&self) -> &[u8];
//     fn as_bytes_with_nul(&self) -> &[u8] where [u8; Self::NUL_TERMINATED as usize - 1]:;
// }

// macro_rules! str_bounds {
//     ($e: ty, $t: ty) => {
//         [(); {(Self::E as usize + (Self::T as isize * -1 + 1) as usize) - 1}]
//     }
// }
macro_rules! check_term {
    ($slice: expr) => {
        // check is very cheap, nul-terminator could be directly memory sensitive, don't skip in release
        if let [inner @ .., b'\0'] = $slice { inner } else { panic!("string not nul terminated") }
    }
}
pub(crate) use check_term;

pub trait BaseCesu8StrEncoding {
    const ENCODE_NUL: bool;
    const NUL_TERM: bool;

    /// Unsafe transformation into this type. If the type is nul-terminated, that must be included.
    #[doc(hidden)]
    unsafe fn _from_bytes_unchecked(bytes: &[u8]) -> &Self;

    /// All raw bytes, nul-terminator and all, if included
    #[doc(hidden)]
    fn _raw_bytes(&self) -> &[u8];

    /// Produces a byte slice of this string's contents in its native encoding. If this type is nul-terminated, that
    /// terminator is excluded.
    fn as_bytes(&self) -> &[u8] {
        let b = self._raw_bytes();

        if Self::NUL_TERM {
            check_term!(b)
        } else {
            b
        }
    }

    /// Converts this type into a UTF-8 string, allocating only when necessary.
    /// 
    /// To try converting this to a string and receving an error if not possible, try
    /// `std::str::from_utf8(mutf8str.as_bytes())`
    fn to_str(&self) -> Cow<str> where [(); Self::ENCODE_NUL as usize]: {
        // SAFETY: any types implementing this trait should be valid cesu8
        unsafe { prims::cesu8_to_utf8::<{Self::ENCODE_NUL}>(Cow::Borrowed(self.as_bytes())) }
    }

    /// The length of this string in bytes. If this string includes a nul-terminator, that is not included.
    fn len(&self) -> usize {
        self.as_bytes().len()
    }
}
pub trait Cesu8StrEncoding: BaseCesu8StrEncoding + ToOwned
where
    Self::Owned: Cesu8StringEncoding + Deref<Target = Self>
{
    /// Transmutes the byte slice into this string's encoding.
    /// 
    /// # Safety
    /// The byte slice should be valid for this string's encoding. See each type's documentation for more information
    /// regarding their encoding invariants.
    unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self where [(); Self::ENCODE_NUL as usize]: {
        if cfg!(debug_assertions) {
            if let Err(e) = Self::try_from_bytes(bytes) {
                panic!("bad string passed to from_bytes_unchecked: {:?}", e);
            }
        }
        
        Self::_from_bytes_unchecked(bytes)
    }

    fn try_from_bytes(b: &[u8]) -> Result<&Self, crate::ngstr::prims::EncodingError> where [(); Self::ENCODE_NUL as usize]: {
        prims::validate_cesu8::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(b)
            .map(|()| unsafe { Self::_from_bytes_unchecked(b) })
    }
    
    fn try_from_utf8(s: &str) -> Result<&Self, usize> where [(); Self::ENCODE_NUL as usize]: {
        match prims::check_utf8_to_cesu8::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(s.as_bytes()) {
            None => Ok(unsafe { Self::from_bytes_unchecked(s.as_bytes()) }),
            Some(idx) => Err(idx)
        }
    }
    fn from_utf8(s: &str) -> Cow<Self> where [(); Self::ENCODE_NUL as usize]: {
        match prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(Cow::Borrowed(s)) {
            Cow::Borrowed(b) => Cow::Borrowed(unsafe { Self::_from_bytes_unchecked(b) }),
            Cow::Owned(b) => Cow::Owned(unsafe { Self::Owned::_from_bytes_unchecked(b) }),
        }
    }

}

pub trait Cesu8CStrEncoding: BaseCesu8StrEncoding + ToOwned
where
    Self::Owned: Cesu8CStringEncoding + Deref<Target = Self>,
{
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
    unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> &Self {
        if cfg!(debug_assertions) {
            match Self::from_bytes_with_nul(bytes) {
                Ok(s) => s,
                Err(e) => panic!("bad string passed to from_bytes_with_nul_unchecked: {:?}", e)
            }
        } else {
            // cheap nul terminator check
            check_term!(bytes);

            // SAFETY: User has guarenteed our invariants
            Self::_from_bytes_unchecked(bytes)
        }
    }

    fn from_bytes_with_nul(b: &[u8]) -> Result<&Self, NGCesu8CError> {
        // quick-path if empty or not nul-terminated
        let contents: &[u8] = match b {
            [rest @ .., b'\0'] => Ok(rest),

            // either zero-length or no ending nul byte
            [..] => Err(NGCesu8CError::NotNulTerminated),
        }?;
        
        let () = prims::validate_cesu8::<{prims::DEFAULT_CHUNK}, true>(contents)?;

        // SAFETY: We know it is a valid string. The encoding validates no interior nuls, and the previous
        // check ensures the last byte is a nul terminator. We've also validated for MUTF8
        Ok(unsafe { Self::_from_bytes_unchecked(b) })
    }

    /// Creates an Mutf8CStr that may nor may not allocate. Must be terminated by a singular nul byte. No other nul
    /// bytes may exist in the string. Will only allocate if 4-byte utf8 sequences exist.
    /// 
    /// # Panics
    /// Panics if the string is not terminated with a nul-byte, or contains nul bytes outside the last character.
    #[inline]
    fn from_utf8_with_nul(src: &str) -> Cow<Self> where Self: Clone, [(); Self::ENCODE_NUL as usize]: {
        // since the string is nul terminated, interior nuls must not exist (ie: are encoded)

        let Some(inner) = src.strip_suffix('\0') else {
            panic!("string passed to from_utf8_with_nul not nul terminated: {:?}", src);
        };

        assert!(!inner.contains('\0'), "string passed to from_utf8_with_nul contains interior nul byte(s): {:?}", src);

        match prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(Cow::Borrowed(inner)) {
            Cow::Borrowed(b) => {
                debug_assert_eq!(b, inner.as_bytes());
                // SAFETY: interior bytes were checked valid, "re-add" nul term by using source nul-terminated string
                Cow::Borrowed(unsafe { Self::_from_bytes_unchecked(b) })
            },
            Cow::Owned(mut v) => {
                v.reserve_exact(1);
                v.push(b'\0');
                // SAFETY: interior bytes were re-encoded to valid, and nul-terminator was re-added
                Cow::Owned(unsafe { Self::Owned::_from_bytes_unchecked(v) })
            }
        }
    }

    fn try_from_utf8_with_nul(s: &str) -> Result<&Self, NGCesu8CError> {
        let inner = s.strip_suffix('\0')
            .ok_or(NGCesu8CError::NotNulTerminated)?;

        match prims::check_utf8_to_cesu8::<{prims::DEFAULT_CHUNK}, true>(inner.as_bytes()) {
            Some(valid_up_to) => {
                if let Some(b'\0') = inner.as_bytes().get(valid_up_to+1) {
                    // interior nul
                    Err(NGCesu8CError::InteriorNul(valid_up_to+1))
                } else {
                    // 4-byte utf8 char
                    Err(NGCesu8CError::Encoding(EncodingError {
                        valid_up_to,
                        // error_len = Some(4) is always valid, as &str cannot contain partial code points (None)
                        error_len: Some(4),
                    }))
                }
            }
            None => {
                // SAFETY: we've validated interior bytes. using the source string s ensures that we add
                // back the nul terminator, that we've previously asserted exists.
                Ok(unsafe { Self::_from_bytes_unchecked(s.as_bytes()) })
            }
        }
    }

    /// Wraps a raw C string with a safe wrapper of this strings encoding.
    /// 
    /// # Safety
    /// * The memory pointed to by `ptr` must contain a valid nul terminator at the end of the string.
    /// * `ptr` must be [valid] for reads of bytes up to and including the null terminator.
    ///   In particular:
    ///     * The entire memory range of this `Self` must be contained within a single allocated object
    ///     * `ptr` must be non-null even for a zero-length mutf8 string
    /// * The memory referenced by the returned `Self` must not be mutated for the duration of lifetime `'a`.
    /// * The size of the string is at most `isize::MAX`
    /// 
    /// Note the following additions to the traditional `CStr` type:
    /// * The memory pointed to be `ptr` must be valid according to `Self`'s encoding.
    /// In comparison to UTF-8:
    ///    * (mutf8 only) nul bytes (`'\0'`) are converted to the null byte sequence (`[0xC0, 0x80]`)
    ///    * (cesu8 + mutf8) four-byte codepoints are converted into the appropriate surrogate pairs
    /// 
    /// # Caveat
    ///
    /// The lifetime for the returned slice is inferred from its usage. To prevent accidental misuse,
    /// it's suggested to tie the lifetime to whichever source lifetime is safe in the context,
    /// such as by providing a helper function taking the lifetime of a host value for the slice,
    /// or by explicit annotation.
    /// 
    /// [valid]: core::ptr#safety
    unsafe fn from_ptr<'a>(ptr: *const c_char) -> &'a Self {
        let cs = CStr::from_ptr(ptr);
        
        Self::from_bytes_with_nul(cs.to_bytes_with_nul()).expect("invalid CStr passed to from_bytes_with_nul")
    }

    unsafe fn from_ptr_unchecked<'a>(ptr: *const c_char) -> &'a Self {
        let cs = CStr::from_ptr(ptr);

        Self::from_bytes_with_nul_unchecked(cs.to_bytes_with_nul())
    }

    fn as_bytes_with_nul(&self) -> &[u8] {
        check_term!(self._raw_bytes());
        self._raw_bytes()
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
    fn as_cstr(&self) -> &CStr {
        CStr::from_bytes_with_nul(self.as_bytes_with_nul())
            .expect("encoded C-style string does not fit CStr requirements")
    }

    fn len_with_nul(&self) -> usize {
        self._raw_bytes().len()
    }
}

pub trait BaseCesu8StringEncoding: Sized + Deref
where
    Self::Target: BaseCesu8StrEncoding,
{
    #[doc(hidden)]
    unsafe fn _from_bytes_unchecked(v: Vec<u8>) -> Self;
    #[doc(hidden)]
    fn _into_bytes_unchecked(self) -> Vec<u8>;

    /// Takes a UTF-8 string and converts it into this string's native encoding. If the type is nul-terminated, that is
    /// added.
    fn from_utf8(s: String) -> Self
    where
        [(); Self::Target::ENCODE_NUL as usize]:
    {
        // TODO: optimize for short strings (re-encode into local buf with std::io::Cursor and prims::utf8_to_cesu8_io)
        let cow = prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, {Self::Target::ENCODE_NUL}>(std::borrow::Cow::Owned(s));
        let mut owned = cow.into_owned();
        if Self::Target::NUL_TERM {
            owned.reserve_exact(1);
            owned.push(b'\0');
        }
        unsafe { Self::_from_bytes_unchecked(owned) }
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
    fn into_string(self) -> String
    where
        [(); Self::Target::ENCODE_NUL as usize]:
    {
        let mut s = self._into_bytes_unchecked();
        if Self::Target::NUL_TERM {
            assert_eq!(s.pop(), Some(b'\0'), "last character was not nul terminator in nul terminated string");
        }
        // inner will always be owned variant
        unsafe {
            prims::cesu8_to_utf8::<{Self::Target::ENCODE_NUL}>(Cow::Owned(s))
        }.into_owned()
    }

    /// Validates a byte vector into this string's native encoding. If the validation is successful, and this string is
    /// nul-terminated, that is added.
    fn from_bytes(b: Vec<u8>) -> Result<Self, crate::ngstr::EncodingError>
    where
        [(); Self::Target::ENCODE_NUL as usize]:
    {
        prims::validate_cesu8::<{prims::DEFAULT_CHUNK}, {Self::Target::ENCODE_NUL}>(&b)?;
        let mut b = b;
        if Self::Target::NUL_TERM {
            b.reserve_exact(1);
            b.push(b'\0');
        }
        Ok(unsafe { Self::_from_bytes_unchecked(b) })
    }

    /// Converts an owned buffer into this strings type. If the type incldues a nul-terminator, it is added by
    /// this function.
    /// 
    /// # Safety
    /// The bytes should be valid for the encoding of this string's type.
    unsafe fn from_bytes_unchecked(v: Vec<u8>) -> Self
    where
        [(); Self::Target::ENCODE_NUL as usize]:
    {
        if cfg!(debug_assertions) {
            Self::from_bytes(v)
                .expect("string passed to from_bytes_unchecked is invalid")
        } else {
            let mut v = v;

            if Self::Target::NUL_TERM {
                v.reserve_exact(1);
                v.push(b'\0');
            }

            // SAFETY: we've added a nul terminator, and the caller has asserted the contents are valid
            unsafe { Self::_from_bytes_unchecked(v) }
        }
    }

    /// Consumes this string and returns the underlying byte buffer.
    ///
    /// The buffer will be in the native string's encoding. If this type
    /// uses a nul-terminator, it is not included.
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
    fn into_bytes(self) -> Vec<u8> {
        let mut inner = self._into_bytes_unchecked();
        if Self::Target::NUL_TERM {
            let Some(b'\0') = inner.pop() else {
                panic!("string not nul terminated");
            };
        }
        inner
    }

    fn with_capacity(mut capacity: usize) -> Self {
        if Self::Target::NUL_TERM { capacity += 1; }
        let mut v = Vec::with_capacity(capacity);
        if Self::Target::NUL_TERM { v.push(b'\0'); }
        unsafe { Self::_from_bytes_unchecked(v) }
    }

    // fn into_inner(self) -> Vec<u8>;
}
pub trait Cesu8StringEncoding: BaseCesu8StringEncoding + Deref
where
    Self::Target: Cesu8StrEncoding + ToOwned<Owned = Self>,
{
}
pub trait Cesu8CStringEncoding: BaseCesu8StringEncoding + Deref
where
    Self::Target: Cesu8CStrEncoding + ToOwned<Owned = Self>,
{
    /// Converts a <code>[Vec]<[u8]></code> into this string type without checking the
    /// string's invariants on the given [`Vec`].
    ///
    /// # Safety
    ///
    /// The given [`Vec`] **must** have exactly one nul byte, in the last position.
    /// This means it cannot be empty nor have any other nul byte anywhere else.
    /// It must also consist of a valid encoded bytes for this string.
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
    unsafe fn from_bytes_with_nul_unchecked(v: Vec<u8>) -> Self {
        if cfg!(debug_assertions) {
            Self::Target::from_bytes_with_nul(&v).expect("string passed to from_bytes_with_nul_unchecked is invalid");
        }

        unsafe { Self::_from_bytes_unchecked(v) }
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
    fn from_bytes_with_nul(v: Vec<u8>) -> Result<Self, FromBytesWithNulError> {
        match Self::Target::from_bytes_with_nul(&v) {
            Ok(_) => Ok(
                // SAFETY: We've checked for a nul terminator and mutf8 encoding
                unsafe { Self::_from_bytes_unchecked(v) }
            ),
            Err(err) => Err(FromBytesWithNulError {
                kind: err,
                bytes: v,
            }),
        }
    }

    /// Equivalent to [`into_bytes()`] except that the
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
    fn into_bytes_with_nul(self) -> Vec<u8> {
        self._into_bytes_unchecked()
    }

    /// Converts a UTF8 allocated string into the encoding of this string's type. The allocation is preserved during
    /// re-encoding.
    fn from_utf8_with_nul(mut s: String) -> Self {
        let Some('\0') = s.pop() else {
            panic!("string passed to from_utf8_with_nul did not contain a nul terminator!");
        };
        let raw_cow = prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, true>(Cow::Owned(s));
        let mut raw = raw_cow.into_owned();
        raw.push(b'\0');
        // SAFETY: converted bytes to proper encoding above
        unsafe { Self::from_bytes_with_nul_unchecked(raw) }
    }

    fn into_cstring(self) -> CString {
        unsafe { CString::from_vec_with_nul_unchecked(self._into_bytes_unchecked()) }
    }

    

    /// Consumes this string and transfers ownership to a C caller.
    ///
    /// The pointer which this function returns must be returned to Rust and reconstituted using
    /// this type's [`from_raw`] method to be properly deallocated. Specifically, one
    /// should *not* use the standard C `free()` function to deallocate
    /// this string.
    ///
    /// Failure to call [`Self::from_raw`] will lead to a memory leak.
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
    fn into_raw(self) -> *mut c_char {
        let boxed = self._into_bytes_unchecked().into_boxed_slice();
        Box::into_raw(boxed) as *mut c_char
    }

    /// Retakes ownership of this type that was transferred to C via
    /// [`Self::into_raw`].
    ///
    /// Additionally, the length of the string will be recalculated from the pointer.
    ///
    /// # Safety
    ///
    /// This should only ever be called with a pointer that was earlier
    /// obtained by calling [`Self::into_raw`]. Other usage (e.g., trying to take
    /// ownership of a string that was allocated by foreign code) is likely to lead
    /// to undefined behavior or allocator corruption.
    ///
    /// It should be noted that the length isn't just "recomputed," but that
    /// the recomputed length must match the original length from the
    /// [`Self::into_raw`] call. This means the [`Self::into_raw`]/`from_raw`
    /// methods should not be used when passing the string to C functions that can
    /// modify the string's length. The inner contract of the string being valid mutf8 must
    /// also be preserved.
    ///
    /// > **Note:** If you need to borrow a string that was allocated by
    /// > foreign code, use [`Self`]. If you need to take ownership of
    /// > a string that was allocated by foreign code, you will need to
    /// > make your own provisions for freeing it appropriately, likely
    /// > with the foreign code's API to do that.
    ///
    /// # Examples
    ///
    /// Creates a `Self`, pass ownership to an `extern` function (via raw pointer), then retake
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
    unsafe fn from_raw(ptr: *mut c_char) -> Self {
        // SAFETY: This is called with a pointer that was obtained from a call
        // to `Self::into_raw` and the length and data has not been modified. As such,
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
            Self::_from_bytes_unchecked(Box::from_raw(slice as *mut [c_char] as *mut [u8]).into_vec())
        }
    }
}




