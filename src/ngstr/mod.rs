
// keep four string variants of actual types --
// null_terminated * ref/owned

// use an enum to internally switch between them, and only expose methods that statically
// switch methods - effectively optimizing out the runtime checks for the specific variant

use std::borrow::Cow;
use std::ffi::c_char;
use std::marker::PhantomData;
use std::ops::{Deref, Add, AddAssign};

use self::prims::{EncodingError, BufferUsage};

pub(crate) mod prims;
pub(crate) mod cesu8str;
pub(crate) mod cesu8string;
pub(crate) mod mutf8str;
pub(crate) mod mutf8string;
pub(crate) mod mutf8cstr;
pub(crate) mod mutf8cstring;
pub(crate) mod cross_impls;

/// An error type for creating a Cesu8/Mutf8 CStr/CString
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

/// An error signifying that a buffer was too small, when trying to convert UTF8 to another string type.
/// 
/// This type contains information necessary to continue the conversion into an owned type without repeating checks.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TryFromUtf8Error<'s, S: ?Sized> {
    source_str: &'s str,
    user_buffer: &'s [u8],
    encode_state: BufferUsage,
    _phantom: PhantomData<S>,
}

impl<'s, S: ?Sized> TryFromUtf8Error<'s, S> {
    /// The number of bytes consumed from the source string
    pub fn bytes_read(&self) -> usize {
        self.encode_state.read
    }
    /// The number of bytes written to the destination buffer
    pub fn bytes_written(&self) -> usize {
        self.encode_state.written
    }
    /// The original source string to convert
    pub fn source_str(&self) -> &str {
        self.source_str
    }
    /// The portion of the source string that was converted
    pub fn source_str_used(&self) -> &str {
        &self.source_str[..self.encode_state.read]
    }
    /// The portion of the source string that is left to convert
    pub fn source_str_rest(&self) -> &str {
        &self.source_str[self.encode_state.read..]
    }
    /// The portion of the user buffer that has been encoded. Note that it will not contain a nul-byte, if required
    /// for the string encoding. It should however, be valid other than that (particularly, partial codepoints should
    /// not exist)
    pub fn encoded_bytes(&self) -> &[u8] {
        &self.user_buffer[..self.encode_state.written]
    }
}

macro_rules! impl_try_from_utf8_error_finish {
    ($t: ty, $ownedvariant: literal) => {
        impl<'s> TryFromUtf8Error<'s, $t> {
            /// Finishes the conversion process from a [`str`] that requires conversion, to an owned
            #[doc = concat!("[`", $ownedvariant, "`][prelude::", $ownedvariant,"]")]
            pub fn finish(mut self) -> <$t as ToOwned>::Owned {
                let mut v = Vec::with_capacity(crate::default_cesu8_capacity(self.source_str.len()) + 1);
                v.extend_from_slice(&self.user_buffer[..self.encode_state.written]); // no nul terminator
                
                // vec writer can't fail
                prims::utf8_to_cesu8_io::<{prims::DEFAULT_CHUNK}, {<$t>::ENCODE_NUL}, _>(
                    self.source_str, false, &mut v, &mut self.encode_state
                ).unwrap();
        
                if <$t>::NUL_TERM {
                    v.push(b'\0');
                }
        
                unsafe { <$t as ToOwned>::Owned::_from_bytes_unchecked(v) }
            }
        }
    }
}

impl_try_from_utf8_error_finish!(cesu8str::Cesu8Str, "Cesu8String");
impl_try_from_utf8_error_finish!(mutf8str::Mutf8Str, "Mutf8String");
impl_try_from_utf8_error_finish!(mutf8cstr::Mutf8CStr, "Mutf8CString");

macro_rules! impl_from_error_vec {
    ($e: ident, $errtype: ty, $srcitem: literal) => {
        #[doc = concat!("A possible error value when converting a ", $srcitem, " into the requested string.")]
        #[doc = "\n\nThis acts as a wrapper type for the actual error, and an owned buffer that can be return"]
        #[doc = " the provided allocation."]
        #[derive(Debug, PartialEq, Eq, Clone)]
        pub struct $e {
            kind: $errtype,
            bytes: Vec<u8>,
        }

        impl $e {
            /// The specific kind of error encountered
            pub fn kind(&self) -> $errtype {
                self.kind
            }
            /// Receive the unmodified, originally provided owned byte string
            pub fn into_inner(self) -> Vec<u8> {
                self.bytes
            }
        }
    }
}

impl_from_error_vec!(FromBytesError, EncodingError, "[`Vec<u8>`]");
impl_from_error_vec!(FromBytesWithNulError, NGCesu8CError, "[`Vec<u8>`]");
// impl_from_error_vec!(FromUtf8WithNulError, NGCesu8CError, "[`String`]");

pub mod prelude {
    pub(crate) use crate::ngstr::*;

    // pub(crate) use super::check_term;
    // pub(crate) use super::prims;

    // commonly used in the api
    pub use std::borrow::Cow;
    pub use std::ops::Deref;
    pub use std::ffi::{CStr, CString};

    // crate-internal
    pub use super::cesu8str::Cesu8Str;
    pub use super::cesu8string::Cesu8String;
    pub use super::mutf8str::Mutf8Str;
    pub use super::mutf8string::Mutf8String;
    pub use super::mutf8cstr::Mutf8CStr;
    pub use super::mutf8cstring::Mutf8CString;

    pub use super::NGCesu8CError;
    pub use super::prims::EncodingError;
    pub use super::TryFromUtf8Error;
    pub use super::FromBytesWithNulError;
}

// trait bounds used as a sort of compile time lint, to ensure they are all implemented
// trait bounds inspired by stdlib str/String

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

macro_rules! check_term {
    ($slice: expr) => {
        // check is very cheap, nul-terminator could be directly memory sensitive, don't skip in release
        if let [inner @ .., b'\0'] = $slice { inner } else { panic!("string not nul terminated") }
    }
}
pub(crate) use check_term;

macro_rules! impl_str_encoding_meths {
    (base, $tyname:tt, $nulterm:tt, $encname:literal) => {
        // expects the following functions available
        
        // Unsafe transformation into this type. If the type is nul-terminated, that must be included.
        // unsafe fn _from_bytes_unchecked(bytes: &[u8]) -> &Self;

        // All raw bytes, nul-terminator and all, if included
        // fn _raw_bytes(&self) -> &[u8];


        #[doc = concat!("Converts this ", $encname, " string to a byte slice, with its native encoding.")]
        ///
        #[cfg_attr($nulterm(), doc = "The returned slice will **not** include the trailing nul terminator.")]
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use cesu8str::", stringify!($tyname), ";\n")]
        #[cfg_attr(not($nulterm()), doc = concat!(
            "let cesu = ", stringify!($tyname), "::try_from_bytes(b\"foo\").unwrap();"
        ))]
        #[cfg_attr($nulterm(), doc = concat!(
            "let cesu = ", stringify!($tyname), "::try_from_bytes_with_nul(b\"foo\\0\").unwrap();"
        ))]
        /// assert_eq!(cesu.as_bytes(), b"foo");
        /// ```
        pub fn as_bytes(&self) -> &[u8] {
            let b = self._raw_bytes();

            if Self::NUL_TERM {
                check_term!(b)
            } else {
                b
            }
        }

        #[doc = concat!("Converts this ", $encname, " string into a UTF-8 string, allocating only when necessary.")]
        /// 
        /// To try fallibly converting this to a UTF-8 string, and erroring if conversion is needed, try
        /// `std::str::from_utf8(mutf8str.as_bytes())`
        pub fn to_str(&self) -> Cow<str> {
            // SAFETY: any types implementing this trait should be valid cesu8
            unsafe { prims::cesu8_to_utf8::<{Self::ENCODE_NUL}>(Cow::Borrowed(self.as_bytes())) }
        }

        #[doc = concat!("Attempts to convert a UTF-8 string into ", $encname, ". The returned string")]
        /// can be borrowed from the source UTF-8 string, or from the provided buffer.
        /// 
        /// If the source string is usable as-is, it is cast and returned. If the source string can be converted into
        /// a byte string that fits within the buffer, it is reencoded and returned. Otherwise, if some form of allocation
        /// or a larger buffer is necessary, an error is returned.
        /// 
        /// The returned error can be used to complete the conversion to an owned string, without re-parsing the beginning.
        pub fn try_from_utf8_into_buf<'s>(s: &'s str, buf: &'s mut [u8]) -> Result<&'s Self, TryFromUtf8Error<'s, Self>> {
            
            // try to use the source string as literally as possible
            let valid_up_to = match prims::check_utf8_to_cesu8::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(s.as_bytes()) {
                None if ! Self::NUL_TERM => { // can use source string
                    // can return as is
                    // SAFETY: the written portion was validated as cesu8
                    return Ok(unsafe { Self::_from_bytes_unchecked(s.as_bytes()) });
                },
                None if Self::NUL_TERM && (buf.len() > s.len()) => { // need nul term, buffer large enough
                    // copy into buf, add nul term, good to go
                    buf[..s.len()].copy_from_slice(s.as_bytes());
                    buf[s.len()] = b'\0';

                    // SAFETY: copied validated bytes, and appended necessary nul terminator
                    return Ok(unsafe { Self::_from_bytes_unchecked(buf) });
                },
                None => { // valid string, buffer too small for nul term
                    s.len()
                }
                Some(err_ind) => { // string needs re-encoding, maybe nul-term, maybe enough space or not
                    err_ind
                },
            };
            
            let mut encode_state = BufferUsage::default();

            // do not copy MIN(valid_up_to, buf.len()) because we don't want to copy partial codepoints to the buffer
            if valid_up_to <= buf.len() {
                // copy what we can literally
                buf[..valid_up_to].copy_from_slice(&s.as_bytes()[..valid_up_to]);
                encode_state.inc(valid_up_to);
            }

            // try to convert rest, if we have space
            debug_assert!((encode_state.read < s.len()) || Self::NUL_TERM);
            let allocate = if encode_state.written < buf.len() {
                
                // convert what we can from the source string to UTF8
                let res = {
                    // create local binding for Cursor to consume
                    // Cursor<&mut &mut [u8]> doesn't seem to impl std::io::Write
                    let cbuf: &mut [u8] = &mut *buf;
                    let mut c = std::io::Cursor::new(cbuf);
                    c.set_position(encode_state.written as u64);
                    let res = prims::utf8_to_cesu8_io::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}, _>(s, true, &mut c, &mut encode_state);
                    
                    match res {
                        Ok(_) => debug_assert_eq!(c.position() as usize, encode_state.written, "encoding state write position and cursor position not kept in sync by prims::utf8_to_cesu8_io"),

                        // on error, write_all will return the amount of bytes it /could/ write
                        Err(_) => debug_assert!(c.position() as usize - encode_state.written < 6, "encoding state write position and cursor position not kept in sync by prims::utf8_to_cesu8_io"),
                    }
                    
                    // drop the cursor, 'unwrapping' it to the original user buf
                    res
                };

                match (Self::NUL_TERM, res) {
                    // successful conversion, nul-term needed and we have space for it
                    (true, Ok(_)) if (encode_state.written < buf.len()) => {
                        buf[encode_state.written] = b'\0';
                        encode_state.written += 1;
                        false
                    },
                    (true, Ok(_)) => {
                        // no space for nul term, have to allocate
                        true
                    }
                    (false, Ok(_)) => {
                        // fully converted, no nul terminator necessary
                        false
                    },
                    (_, Err(_)) => {
                        // no space left in buffer, have to allocate
                        true
                    }
                }
            } else {
                // no more space left, have to allocate
                true
            };

            if !allocate {
                let used = &mut buf[..encode_state.written];

                // SAFETY: the written portion was re-encoded as valid cesu8
                // and a nul-terminator was added if necessary
                Ok(unsafe { Self::_from_bytes_unchecked(used) })
            } else {
                Err(TryFromUtf8Error {
                    source_str: s,
                    user_buffer: buf,
                    encode_state,
                    _phantom: PhantomData,
                })
            }
        }

        #[doc = concat!("Converts a UTF-8 string into ", $encname, ". If possible, the string slice will be returned as")]
        /// is. If not, the provided buffer is used. If the string is too big for the buffer, it will be allocated.
        #[inline]
        pub fn from_utf8_into_buf<'s>(s: &'s str, buf: &'s mut [u8]) -> Cow<'s, Self> {
            match Self::try_from_utf8_into_buf(s, buf) {
                Ok(enc) => Cow::Borrowed(enc),
                Err(err) => Cow::Owned(err.finish())
            }
            // let mut c = std::io::Cursor::new(buf);
            // let mut encode_state = BufferUsage::default();
            // let res = prims::utf8_to_cesu8_io::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}, _>(s, false, &mut c, &mut encode_state);
            // let mut allocate = res.is_err();
            // let usrbuf = c.into_inner();

            // if Self::NUL_TERM {
            //     if encode_state.written < usrbuf.len() {
            //         // space for a nul-byte
            //         usrbuf[encode_state.written] = b'\0';
            //         encode_state.written += 1;
            //     } else {
            //         // no space for nul-byte
            //         allocate = true;
            //     }
            // }

            // let used = &mut usrbuf[..encode_state.written];
            // if !allocate {
            //     // SAFETY: the written portion was re-encoded as valid cesu8
            //     // and a nul-terminator was added if necessary
            //     Cow::Borrowed(unsafe { Self::_from_bytes_unchecked(used) })
            // } else {
            //     let mut v = Vec::with_capacity(crate::default_cesu8_capacity(s.len()) + 1);
            //     v.extend_from_slice(used); // no nul terminator
            //     let rest = &s[encode_state.read..];
                
            //     // vec writer can't fail
            //     prims::utf8_to_cesu8_io::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}, _>(s, false, &mut v, &mut encode_state).unwrap();

            //     if Self::NUL_TERM {
            //         v.push(b'\0');
            //     }

            //     Cow::Owned(unsafe { <Self as ToOwned>::Owned::_from_bytes_unchecked(v) })
            // }
        }

        /// The length of this string in bytes.
        #[cfg_attr($nulterm(), doc = " The nul-terminator is not included.")]
        pub fn len(&self) -> usize {
            self.as_bytes().len()
        }

        /// Returns `true` if [`as_bytes()`][Self::as_bytes]` has a length of 0.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("use cesu8str::", stringify!($tyname), ";\n")]
        /// # use cesu8str::NGCesu8CError;
        ///
        /// # fn main() { test().unwrap(); }
        #[cfg_attr($nulterm(), doc = concat!("
# fn test() -> Result<(), NGCesu8CError> {
let empty = Mutf8CStr::try_from_bytes_with_nul(b\"\\0\")?;
assert!(empty.is_empty()); // nul-terminator isn't included

let foo = Mutf8CStr::try_from_bytes_with_nul(b\"foo\\0\")?;
assert!(!foo.is_empty());"))]
        #[cfg_attr(not($nulterm()), doc = concat!("
# fn test() -> Result<(), NGCesu8CError> {
let empty = ", stringify!($tyname), "::try_from_bytes(b\"\")?;
assert!(empty.is_empty());

let foo = ", stringify!($tyname), "::try_from_bytes(b\"foo\")?;
assert!(!foo.is_empty());"))]
        /// # Ok(())
        /// # }
        /// ```
        pub fn is_empty(&self) -> bool {
            self.as_bytes().is_empty()
        }

        #[doc = concat!("Checks that `index`-th byte is the first byte in a ", $encname, " code point")]
        /// sequence or the end of the string.
        ///
        /// The start and end of the string (when `index == self.len()`) are
        /// considered to be boundaries.
        ///
        /// Returns `false` if `index` is greater than `self.len()`.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use cesu8str::", stringify!($tyname), "ing;")]
        #[doc = concat!("let s = ", stringify!($tyname), "ing::from_utf8(\"Löwe 老虎 Léopard\".to_owned());")]
        /// assert!(s.is_char_boundary(0));
        /// // start of `老`
        /// assert!(s.is_char_boundary(6));
        /// assert!(s.is_char_boundary(s.len()));
        ///
        /// // second byte of `ö`
        /// assert!(!s.is_char_boundary(2));
        ///
        /// // third byte of `老`
        /// assert!(!s.is_char_boundary(8));
        /// ```
        pub fn is_char_boundary(&self, index: usize) -> bool {
            if index == 0 { return true; }
            match self.as_bytes().get(index) {
                None => index == self.len(),
                Some(0xED) => {
                    // this is a valid string - there are at least three bytes available
                    let surrogate_pair_one = &self.as_bytes()[index..index+3];
                    if std::str::from_utf8(surrogate_pair_one).is_ok() {
                        // a three-byte UTF8 sequence
                        true
                    } else {
                        // part of a six-byte surrogate pair

                        // this function is used to test where things can be inserted into
                        // don't allow inserting in the middle of a surrogate pair
                        // also must account for multiple pairs in a row
                        todo!("is_char_boundary on surrogate pair, test if second codepoint or not");
                        // start with `0` or `11`
                    }
                },
                // https://github.com/rust-lang/rust/blob/938afba8996fe058b91c61b23ef5d000cb9ac169/library/core/src/num/mod.rs#L1016
                Some(&b) => (b as i8) >= -0x40,
            }
        }
    };
    (str, $tyname:tt, $nulterm:tt, $encname:literal) => {
        #[doc = concat!("Transmutes the byte slice into ", $encname,".")]
        /// 
        /// # Safety
        #[doc = concat!("The byte slice must be valid ", $encname)]
        #[cfg_attr($nulterm(), doc = ", including the nul-terminator")]
        #[doc = concat!(". See [", stringify!($tyname), "][cesu8str::", stringify!($tyname), "] for more information regarding their encoding and invariants.")]
        pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
            if cfg!(debug_assertions) {
                if let Err(e) = Self::try_from_bytes(bytes) {
                    panic!("bad string passed to from_bytes_unchecked: {:?}", e);
                }
            }
            
            Self::_from_bytes_unchecked(bytes)
        }

        #[doc = concat!("Validates a byte slice as ", $encname, ". This will never allocate.")]
        /// If an error occurs, position information is returned through the [`EncodingError`]
        pub fn try_from_bytes(b: &[u8]) -> Result<&Self, crate::ngstr::prims::EncodingError> {
            prims::validate_cesu8::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(b)
                .map(|()| unsafe { Self::_from_bytes_unchecked(b) })
        }

        /// Validates a byte slice into this string. This will never allocate. If an error occurs, position information
        /// is returned through the Err variant.
        /// 
        /// Since UTF-8 can always be converted, if this errors then using another buffer/allocating is necessary.
        pub fn try_from_utf8(s: &str) -> Result<&Self, usize> {
            match prims::check_utf8_to_cesu8::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(s.as_bytes()) {
                None => Ok(unsafe { Self::from_bytes_unchecked(s.as_bytes()) }),
                Some(idx) => Err(idx)
            }
        }

        /// Converts the UTF8 string into this type's string encoding. If possible, the original string is validated
        /// and returned as-is, but if it needs to be reallocated, then it will return an owned variant.
        pub fn from_utf8(s: &str) -> Cow<Self> {
            match prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(Cow::Borrowed(s)) {
                Cow::Borrowed(b) => Cow::Borrowed(unsafe { Self::_from_bytes_unchecked(b) }),
                Cow::Owned(b) => Cow::Owned(unsafe { <Self as ToOwned>::Owned::_from_bytes_unchecked(b) }),
            }
        }

        /// Encodes a UTF8 string into this string's native encoding, directly into the provided writer. The encoding
        /// process is infallible so any errors will be from the underlying `std::io::Write`'r.
        #[inline]
        pub fn encode_utf8_into_writer<W: std::io::Write + fmt::Debug>(s: &str, w: W) -> std::io::Result<usize> {
            // not available for cstr's to make null-terminator exclusion explicit
            prims::utf8_to_cesu8_io::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}, W>(s, false, w, &mut BufferUsage::default()).map(|bu| bu.written)
        }
    };
    (cstr, $tyname:tt, $nulterm:tt, $encname:literal) => {
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
        ///     let mutf8cstr = Mutf8CStr::from_bytes_with_nul_unchecked(mutf8cstring.as_bytes_with_nul());
        ///     assert_eq!(mutf8cstr, &*mutf8cstring);
        /// }
        /// ```
        pub unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> &Self {
            if cfg!(debug_assertions) {
                match Self::try_from_bytes_with_nul(bytes) {
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

        /// Creates an MUTF-8 C string wrapper from a byte slice.
        ///
        /// This function will cast the provided `bytes` to a `Mutf8CStr`
        /// wrapper after ensuring that the byte slice is nul-terminated
        /// and does not contain any interior nul bytes. This also checks
        /// for MUTF-8 compliance.
        ///
        // /// If the nul byte may not be at the end,
        // /// [`Mutf8CStr::from_bytes_until_nul`] can be used instead.
        // ///
        /// # Examples
        ///
        /// ```
        /// use cesu8str::Mutf8CStr;
        ///
        /// let mutf8cstr = Mutf8CStr::try_from_bytes_with_nul(b"hello\0");
        /// assert!(mutf8cstr.is_ok());
        /// ```
        ///
        /// Creating a `Mutf8CStr` without a trailing nul terminator is an error:
        ///
        /// ```
        /// use cesu8str::Mutf8CStr;
        ///
        /// let mutf8cstr = Mutf8CStr::try_from_bytes_with_nul(b"hello");
        /// assert!(mutf8cstr.is_err());
        /// ```
        ///
        /// Creating a `CStr` with an interior nul byte is an error:
        ///
        /// ```
        /// use cesu8str::Mutf8CStr;
        ///
        /// let mutf8cstr = Mutf8CStr::try_from_bytes_with_nul(b"he\0llo\0");
        /// assert!(mutf8cstr.is_err());
        /// ```
        pub fn try_from_bytes_with_nul(b: &[u8]) -> Result<&Self, NGCesu8CError> {
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
        pub fn from_utf8_with_nul(src: &str) -> Cow<Self> {
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
                    Cow::Owned(unsafe { <Self as ToOwned>::Owned::_from_bytes_unchecked(v) })
                }
            }
        }

        /// Attempts to validate UTF-8 as a nul-terminated MUTF-8 string. If this isn't possible, an error is returned.
        /// 
        /// Requirements
        /// - The last byte **must** by a nul-byte.
        /// - There must not be other interior nul-bytes.
        /// - There are no four-byte UTF-8 sequences.
        pub fn try_from_utf8_with_nul(s: &str) -> Result<&Self, NGCesu8CError> {
            let inner = s.strip_suffix('\0')
                .ok_or(NGCesu8CError::NotNulTerminated)?;

            match prims::check_utf8_to_cesu8::<{prims::DEFAULT_CHUNK}, {Self::ENCODE_NUL}>(inner.as_bytes()) {
                Some(valid_up_to) => {
                    if let Some(b'\0') = inner.as_bytes().get(valid_up_to+1) {
                        // interior nul
                        Err(NGCesu8CError::InteriorNul(valid_up_to+1))
                    } else {
                        // 4-byte utf8 char
                        Err(NGCesu8CError::Encoding(EncodingError {
                            valid_up_to,
                            // error_len = Some(4) is always valid, as &str cannot contain partial code points (None)
                            error_len: Some(4.try_into().unwrap()),
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
        ///    * (mutf8 only) nul bytes (`'\0'`) are converted to the null byte sequence (`b"\xC0\x80"`)
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
        pub unsafe fn from_ptr<'a>(ptr: *const c_char) -> &'a Self {
            let cs = CStr::from_ptr(ptr);
            
            Self::try_from_bytes_with_nul(cs.to_bytes_with_nul()).expect("invalid CStr passed to from_bytes_with_nul")
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
        ///    * (mutf8 only) nul bytes (`'\0'`) are converted to the null byte sequence (`b"\xC0\x80"`)
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
        pub unsafe fn from_ptr_unchecked<'a>(ptr: *const c_char) -> &'a Self {
            let cs = CStr::from_ptr(ptr);

            Self::from_bytes_with_nul_unchecked(cs.to_bytes_with_nul())
        }

        /// Converts this MUTF-8 C string to a byte slice containing the trailing 0 byte.
        ///
        /// This function is the equivalent of [`Mutf8CStr::as_bytes`] except that it
        /// will retain the trailing nul terminator instead of chopping it off.
        ///
        /// # Examples
        ///
        /// ```
        /// use cesu8str::Mutf8CStr;
        ///
        /// let mutf8str = Mutf8CStr::try_from_bytes_with_nul(b"foo\0").expect("Mutf8CStr::try_from_bytes_with_nul failed");
        /// assert_eq!(mutf8str.as_bytes_with_nul(), b"foo\0");
        /// ```
        pub fn as_bytes_with_nul(&self) -> &[u8] {
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
        pub fn as_cstr(&self) -> &CStr {
            CStr::from_bytes_with_nul(self.as_bytes_with_nul())
                .expect("encoded C-style string does not fit CStr requirements")
        }

        /// Returns the size of the string in bytes, including the nul byte.
        pub fn len_with_nul(&self) -> usize {
            self._raw_bytes().len()
        }

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
    };
}

macro_rules! impl_string_encoding_meths {
    (base, $encname:literal) => {
        // expects these functions
        // #[doc(hidden)]
        // unsafe fn _from_bytes_unchecked(v: Vec<u8>) -> Self;
        // #[doc(hidden)]
        // fn _into_bytes_unchecked(self) -> Vec<u8>;

        /// Takes a UTF-8 string and converts it into this string's native encoding. If the type is nul-terminated, that is
        /// added.
        pub fn from_utf8(s: String) -> Self {
            // TODO: optimize for short strings (re-encode into local buf with std::io::Cursor and prims::utf8_to_cesu8_io)
            let cow = prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, {<Self as Deref>::Target::NUL_TERM}>(std::borrow::Cow::Owned(s));
            let mut owned = cow.into_owned();
            if <Self as Deref>::Target::NUL_TERM {
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
        pub fn into_string(self) -> String {
            let mut s = self._into_bytes_unchecked();
            if <Self as Deref>::Target::NUL_TERM {
                assert_eq!(s.pop(), Some(b'\0'), "last character was not nul terminator in nul terminated string");
            }
            // inner will always be owned variant
            unsafe {
                prims::cesu8_to_utf8::<{<Self as Deref>::Target::ENCODE_NUL}>(Cow::Owned(s))
            }.into_owned()
        }

        /// Validates a byte vector into this string's native encoding. If the validation is successful, and this string is
        /// nul-terminated, that is added.
        pub fn try_from_bytes(b: Vec<u8>) -> Result<Self, FromBytesError> {
            if let Err(e) = prims::validate_cesu8::<{prims::DEFAULT_CHUNK}, {<Self as Deref>::Target::ENCODE_NUL}>(&b) {
                return Err(FromBytesError { kind: e, bytes: b });
            }
            let mut b = b;
            if <Self as Deref>::Target::NUL_TERM {
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
        pub unsafe fn from_bytes_unchecked(v: Vec<u8>) -> Self {
            if cfg!(debug_assertions) {
                Self::try_from_bytes(v)
                    .expect("string passed to from_bytes_unchecked is invalid")
            } else {
                let mut v = v;

                if <Self as Deref>::Target::NUL_TERM {
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
        pub fn into_bytes(self) -> Vec<u8> {
            let mut inner = self._into_bytes_unchecked();
            if <Self as Deref>::Target::NUL_TERM {
                check_term!(inner.as_slice());
                inner.pop().unwrap();
            }
            inner
        }

        /// Create an owned string with pre-allocated capacity.
        /// 
        /// If applicable, the provided capacity count does not include a nul-terminator.
        pub fn with_capacity(mut capacity: usize) -> Self {
            if <Self as Deref>::Target::NUL_TERM { capacity += 1; }
            let mut v = Vec::with_capacity(capacity);
            if <Self as Deref>::Target::NUL_TERM { v.push(b'\0'); }
            unsafe { Self::_from_bytes_unchecked(v) }
        }

        /// Returns the size of the internal allocation for this string.
        /// 
        /// Note that unlike [`with_capacity`][Self::with_capacity], this includes the nul-terminator when applicable.
        pub fn capacity(&self) -> usize {
            self.inner.capacity()
        }

        /// Encodes a UTF-8 string and inserts it into this string at the provided index.
        /// 
        /// The index may not lie within a character boundary.
        pub fn insert_str(&mut self, idx: usize, string: &str) {
            assert!(self.is_char_boundary(idx), "provided index is not a valid character boundary");

            let nt = <Self as Deref>::Target::NUL_TERM;
            if idx == self.as_bytes().len() {
                // if we're writing to the end, we can just Write directly into our own buffer
                // after accounting for possible nul-terminator

                if nt {
                    check_term!(self.inner.as_slice());
                    self.inner.pop().unwrap();
                }
                // writing to vec, cannot fail
                prims::utf8_to_cesu8_io::<{prims::DEFAULT_CHUNK}, {<Self as Deref>::Target::ENCODE_NUL}, _>(string, false, &mut self.inner, &mut BufferUsage::default()).unwrap();
                if nt {
                    self.inner.push(b'\0');
                }
            } else {
                // re-encode it, and splice it in
                // let encoded = <Self as Deref>::Target::from_utf8(string);
                let encoded = prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, {<Self as Deref>::Target::ENCODE_NUL}>(Cow::Borrowed(string));
                self.inner.splice(idx..idx, encoded.iter().copied());
            }
        }
        
        /// Insert this string at the specified index.
        /// 
        /// # Panics
        /// If the index is on a character boundary.
        pub fn insert_at(&mut self, idx: usize, string: &<Self as Deref>::Target) {
            assert!(self.is_char_boundary(idx), "provided index is not a valid character boundary");
            // as_bytes leaves out the nul-terminator if necessary
            self.inner.splice(idx..idx, string.as_bytes().iter().copied());
        }

        // fn into_inner(self) -> Vec<u8>;
    };
    (string, $encname:literal) => {

    };
    (cstring, $encname:literal) => {
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
        ///     unsafe { Mutf8CString::from_bytes_with_nul_unchecked(b"abc\0".to_vec()) },
        ///     unsafe { Mutf8CString::from_bytes_unchecked(b"abc".to_vec()) }
        /// );
        /// ```
        pub unsafe fn from_bytes_with_nul_unchecked(v: Vec<u8>) -> Self {
            if cfg!(debug_assertions) {
                <Self as Deref>::Target::try_from_bytes_with_nul(&v).expect("string passed to from_bytes_with_nul_unchecked is invalid");
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
        ///     Mutf8CString::try_from_bytes_with_nul(b"abc\0".to_vec())
        ///         .expect("Mutf8CString::try_from_bytes_with_nul failed unexpectedly"),
        ///     Mutf8CString::new(b"abc".to_vec()).expect("Mutf8CString::new failed")
        /// );
        /// ```
        ///
        /// An incorrectly formatted [`Vec`] will produce an error.
        ///
        /// ```
        /// use cesu8str::{Mutf8CString, FromBytesWithNulError};
        /// // Interior nul byte
        /// let _: FromBytesWithNulError = Mutf8CString::try_from_bytes_with_nul(b"a\0bc".to_vec()).unwrap_err();
        /// // No nul byte
        /// let _: FromBytesWithNulError = Mutf8CString::try_from_bytes_with_nul(b"abc".to_vec()).unwrap_err();
        /// ```
        pub fn try_from_bytes_with_nul(v: Vec<u8>) -> Result<Self, FromBytesWithNulError> {
            match <Self as Deref>::Target::try_from_bytes_with_nul(&v) {
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

        /// Equivalent to [`Mutf8String::into_bytes()`] except that the
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
            self._into_bytes_unchecked()
        }

        /// Converts a UTF8 allocated string into the encoding of this string's type. The allocation is preserved during
        /// re-encoding.
        pub fn from_utf8_with_nul(mut s: String) -> Self {
            let Some('\0') = s.pop() else {
                panic!("string passed to from_utf8_with_nul did not contain a nul terminator!");
            };
            let raw_cow = prims::utf8_to_cesu8_vec::<{prims::DEFAULT_CHUNK}, true>(Cow::Owned(s));
            let mut raw = raw_cow.into_owned();
            raw.push(b'\0');
            // SAFETY: converted bytes to proper encoding above
            unsafe { Self::from_bytes_with_nul_unchecked(raw) }
        }

        /// Converts this string to a CString, preserving the internal allocation.
        pub fn into_cstring(self) -> CString {
            unsafe { CString::from_vec_with_nul_unchecked(self._into_bytes_unchecked()) }
        }

        /// Consumes this string and transfers ownership to a C caller.
        ///
        /// The pointer which this function returns must be returned to Rust and reconstituted using
        /// this type's [`from_raw`] method to be properly deallocated. Specifically, one
        /// should *not* use the standard C `free()` function to deallocate
        /// this string.
        ///
        /// Failure to call [`from_raw`] will lead to a memory leak.
        ///
        /// The C side must **not** modify the length of the string (by writing a
        /// `null` somewhere inside the string or removing the final one) before
        /// it makes it back into Rust using [`from_raw`]. See the safety section
        /// in [`from_raw`].
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
        /// 
        /// [`from_raw`]: Self::from_raw
        #[must_use = "`self` will be dropped if the result is not used"]
        pub fn into_raw(self) -> *mut c_char {
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
        pub unsafe fn from_raw(ptr: *mut c_char) -> Self {
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
    };
}

macro_rules! impl_simple_str_traits {
    (base $S:ty, $encname:literal) => {
        impl fmt::Debug for $S {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <str as fmt::Debug>::fmt(&self.to_str(), f)
            }
        }
        impl fmt::Display for $S {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <str as fmt::Display>::fmt(&self.to_str(), f)
            }
        }
        impl Hash for $S {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                self.to_str().hash(state);
            }
        }
    };
    (str $S:ty, $encname:literal) => {
        impl<'a> Add<&'_ str> for &$S {
            type Output = <$S as ToOwned>::Owned;
            fn add(self, rhs: &str) -> Self::Output {
                self.to_owned() + rhs
            }
        }
        impl<'a> Add<&'_ $S> for &$S {
            type Output = <$S as ToOwned>::Owned;
            fn add(self, rhs: &$S) -> Self::Output {
                self.to_owned() + rhs
            }
        }
        impl<'a> Add<&'_ $S> for String {
            type Output = String;
            fn add(mut self, rhs: &$S) -> Self {
                self.push_str(&rhs.to_str());
                self
            }
        }
        impl<'a> Add<&'_ $S> for Cow<'a, $S> {
            type Output = Self;
            fn add(self, rhs: &$S) -> Self {
                if rhs.is_empty() { return self; }
                Cow::Owned(self.into_owned() + rhs)
            }
        }
    };
    (string $S:ty, $encname:literal) => {
        impl From<String> for $S {
            fn from(s: String) -> $S {
                <$S>::from_utf8(s)
            }
        }
        impl From<&'_ str> for $S {
            fn from(s: &str) -> $S {
                <$S>::from_utf8(s.to_string())
            }
        }
        impl From<$S> for String {
            fn from(s: $S) -> Self {
                s.into_string()
            }
        }
        impl Add<&'_ str> for $S {
            type Output = $S;
            fn add(mut self, rhs: &str) -> Self::Output {
                self += rhs;
                self
            }
        }
        impl Add<&'_ <$S as Deref>::Target> for $S {
            type Output = $S;
            fn add(mut self, rhs: &<$S as Deref>::Target) -> Self::Output {
                self += rhs;
                self
            }
        }
        impl AddAssign<&'_ str> for $S {
            fn add_assign(&mut self, rhs: &str) {
                self.insert_str(self.len(), rhs)
            }
        }
        impl AddAssign<&'_ <$S as Deref>::Target> for $S {
            fn add_assign(&mut self, rhs: &'_ <$S as Deref>::Target) {
                self.insert_at(self.len(), rhs)
            }
        }

        impl fmt::Write for $S {
            #[inline]
            fn write_str(&mut self, s: &str) -> fmt::Result {
                *self += s;
                Ok(())
            }
        }
    }
}

use std::fmt;
use std::hash::Hash;
impl_simple_str_traits!(base cesu8str::Cesu8Str, "CESU-8");
impl_simple_str_traits!(base mutf8str::Mutf8Str, "MUTF-8");
impl_simple_str_traits!(base mutf8cstr::Mutf8CStr, "MUTF-8");
impl_simple_str_traits!(str cesu8str::Cesu8Str, "CESU-8");
impl_simple_str_traits!(str mutf8str::Mutf8Str, "MUTF-8");
impl_simple_str_traits!(str mutf8cstr::Mutf8CStr, "MUTF-8");

impl_simple_str_traits!(base cesu8string::Cesu8String, "CESU-8");
impl_simple_str_traits!(base mutf8string::Mutf8String, "MUTF-8");
impl_simple_str_traits!(base mutf8cstring::Mutf8CString, "MUTF-8");
impl_simple_str_traits!(string cesu8string::Cesu8String, "CESU-8");
impl_simple_str_traits!(string mutf8string::Mutf8String, "MUTF-8");
impl_simple_str_traits!(string mutf8cstring::Mutf8CString, "MUTF-8");

impl<'b> TryFrom<&'b [u8]> for &'b cesu8str::Cesu8Str {
    type Error = EncodingError;
    fn try_from(value: &'b [u8]) -> Result<Self, Self::Error> {
        cesu8str::Cesu8Str::try_from_bytes(value)
    }
}
impl<'b> TryFrom<&'b [u8]> for &'b mutf8str::Mutf8Str {
    type Error = EncodingError;
    fn try_from(value: &'b [u8]) -> Result<Self, Self::Error> {
        mutf8str::Mutf8Str::try_from_bytes(value)
    }
}
impl TryFrom<Vec<u8>> for cesu8string::Cesu8String {
    type Error = FromBytesError;
    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        cesu8string::Cesu8String::try_from_bytes(value)
    }
}
impl TryFrom<Vec<u8>> for mutf8string::Mutf8String {
    type Error = FromBytesError;
    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        mutf8string::Mutf8String::try_from_bytes(value)
    }
}

#[test]
fn strings_impl_expected_traits() {
    use crate::prelude::*;
    
    // check for some common trait impls that should assist in general usability

    /// most operator-based in [`crate::ngstr::cross_impls`]
    trait ExpectedTraitsBorrowed<'s, SB:
        ?Sized
        + fmt::Debug + fmt::Display + std::hash::Hash + ToOwned
        // + PartialEq<str> + PartialEq<SB>
        // + PartialOrd<str> + PartialOrd<SB>
        
        
    > where
        for<'b> &'b SB: Add<&'b str, Output = <SB as ToOwned>::Owned>,
    {}
    trait ExpectedTraitsOwned<SO:
        Sized
        + fmt::Debug + fmt::Display + std::hash::Hash + Deref + Clone
        // + PartialEq<str> + PartialEq<SO>
        // + PartialOrd<str> + PartialOrd<SO>
        
        + From<String> + Into<String>
    > where
        for<'s> SO: Add<&'s str, Output = SO>,
        for<'s> SO: Add<&'s <SO as Deref>::Target, Output = SO>,
        for<'s> SO: AddAssign<&'s str> + AddAssign<&'s <SO as Deref>::Target>,
        for<'s> SO: From<&'s str> + From<String>,
    {}

    // will not compile if test 'fails'
    impl ExpectedTraitsBorrowed<'_, Cesu8Str> for () {}
    impl ExpectedTraitsBorrowed<'_, Mutf8Str> for () {}
    impl ExpectedTraitsBorrowed<'_, Mutf8CStr> for () {}
    impl ExpectedTraitsOwned<Cesu8String> for () {}
    impl ExpectedTraitsOwned<Mutf8String> for () {}
    impl ExpectedTraitsOwned<Mutf8CString> for () {}
}

pub(crate) use {impl_str_encoding_meths, impl_string_encoding_meths, impl_simple_str_traits};
