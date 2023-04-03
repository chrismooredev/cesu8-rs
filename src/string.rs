#![allow(deprecated)]

use std::borrow::Cow;
use std::io;
use std::str::Utf8Error;

use crate::decoding;
use crate::from_utf8_slice;
use crate::from_utf8_vec;
use crate::encoding;
use crate::encoding::utf8err_inc;
use crate::Cesu8Error;
use crate::Variant;

const UTF8_REPLACEMENT_CHAR: &[u8] = "\u{FFFD}".as_bytes();
#[test]
fn valid_replacement_char() {
    let mut buf = [0; 4];
    let as_bytes = std::char::REPLACEMENT_CHARACTER
        .encode_utf8(&mut buf)
        .as_bytes();
    assert_eq!(
        as_bytes, UTF8_REPLACEMENT_CHAR,
        "internal 'cached' UTF8_REPLACEMENT_CHAR differs from the standard library"
    );
}

/// A CESU-8 or Modified UTF-8 string.
///
/// The main difference between a CESU-8/MUTF-8 string and a regular UTF-8 string is
/// in handling of 4-byte long (in UTF-8) characters. For CESU-8/MUTF-8, these characters
/// are instead encoded as two, three-byte long UTF-16 characters.
///
/// CESU-8 and MUTF-8 strings are encoded the same, except that MUTF-8 strings, as used by
/// the JVM and JNI applications, encode a nul byte (hex `00`) as a UTF-8 2-byte zero
/// character (hex `C0 80`)
#[derive(Clone)]
#[deprecated(since = "0.1.3", note = "use cesu8str::Mutf8CStr or cesu8str::Mutf8CString")]
pub struct Cesu8Str<'s> {
    pub(crate) variant: Variant,

    /// If the data within `self.bytes` is also valid UTF-8
    pub(crate) utf8_error: Result<(), Utf8Error>,

    /// The contained string data. If modified, `self.is_utf8` must be updated.
    pub(crate) bytes: Cow<'s, [u8]>,
}

impl<'s> Cesu8Str<'s> {
    /// Returns the CESU8 variant this string is encoded in.
    pub const fn variant(&self) -> Variant {
        self.variant
    }

    /// If the string is invalid UTF-8, this returns the UTF-8 error that would occur, given `str::from_utf8(cesu8.as_bytes()).unwrap_err()`
    ///
    /// # Examples
    /// * Example 1: A valid UTF8/Ascii string
    /// ```
    /// # use std::str;
    /// # use cesu8str::{Cesu8Str, Variant};
    /// const VALID_UTF8: &[u8] = b"my valid string";
    /// let as_str = str::from_utf8(VALID_UTF8).map(|_| ());
    /// let as_cesu8 = Cesu8Str::from_cesu8(VALID_UTF8, Variant::Standard).unwrap();
    /// assert_eq!(as_str, as_cesu8.utf8_error());
    /// assert!(as_str.is_ok());
    /// ```
    /// * Example 2: Embedded Nuls are invalid UTF8
    /// ```
    /// # use std::str;
    /// # use cesu8str::{Cesu8Str, Variant};
    /// const INVALID_UTF8: &[u8] = b"with embedded \xC0\x80 null";
    /// let as_str = str::from_utf8(INVALID_UTF8).map(|_| ());
    /// let as_cesu8 = Cesu8Str::from_cesu8(INVALID_UTF8, Variant::Java).unwrap();
    /// assert_eq!(as_str, as_cesu8.utf8_error());
    /// let utf8_err = as_str.unwrap_err();
    /// assert_eq!(14, utf8_err.valid_up_to());
    /// assert_eq!(Some(1), utf8_err.error_len());
    /// ```
    pub const fn utf8_error(&self) -> Result<(), Utf8Error> {
        self.utf8_error
    }

    /// Ensures the string is owned to allievate any lifetime issues
    pub fn into_owned(self) -> Cesu8Str<'static> {
        let owned: Vec<u8> = match self.bytes {
            Cow::Borrowed(s) => s.to_owned(),
            Cow::Owned(v) => v,
        };
        Cesu8Str {
            variant: self.variant,
            utf8_error: self.utf8_error,
            bytes: Cow::Owned(owned),
        }
    }

    /// Validates a sequence of bytes as CESU8, will not allocate.
    ///
    /// # Examples
    /// ### Valid CESU-8, Valid UTF-8, Valid ascii
    /// ```
    /// # use std::str::from_utf8;
    /// # use cesu8str::{Cesu8Str, Variant};
    /// const ASCII: &[u8] = b"normal ascii string";
    /// let as_cesu8 = Cesu8Str::from_cesu8(ASCII, Variant::Standard).unwrap();
    ///
    /// // There were no UTF-8 errors within the string
    /// assert_eq!(from_utf8(ASCII).map(|_| ()), as_cesu8.utf8_error());
    /// assert_eq!(as_cesu8.utf8_error(), Ok(()));
    /// ```
    ///
    /// ### Valid CESU-8, Invalid UTF-8
    /// ```
    /// # use std::str::from_utf8;
    /// # use cesu8str::{Cesu8Str, Variant};
    /// const VALID_CESU8: &[u8] = b"with embedded \xC0\x80 null";
    /// let as_cesu8 = Cesu8Str::from_cesu8(VALID_CESU8, Variant::Java).unwrap();
    ///
    /// // It's not valid UTF-8, check the utf8_error
    /// assert_eq!(from_utf8(VALID_CESU8).map(|_| ()), as_cesu8.utf8_error());
    /// let utf8_err = as_cesu8.utf8_error().unwrap_err();
    /// assert_eq!(14, utf8_err.valid_up_to());
    /// assert_eq!(Some(1), utf8_err.error_len());
    /// ```
    ///
    /// ### Invalid CESU-8, Invalid UTF-8
    /// ```
    /// # use std::str::from_utf8;
    /// # use cesu8str::{Cesu8Str, Variant};
    /// const INVALID_CESU8: &[u8] = b"with embedded \xC0\x80 null"; // is valid Java variant, but test with Standard so it's invalid
    /// let as_cesu8_err = Cesu8Str::from_cesu8(INVALID_CESU8, Variant::Standard).unwrap_err();
    /// assert_eq!(14, as_cesu8_err.valid_up_to());
    /// assert_eq!(from_utf8(INVALID_CESU8).map(|_| ()), as_cesu8_err.utf8_error());
    ///
    ///
    /// let valid = &INVALID_CESU8[..as_cesu8_err.valid_up_to()];
    /// let as_cesu8 = Cesu8Str::from_cesu8(valid, Variant::Standard).unwrap();
    /// assert_eq!(from_utf8(valid).map(|_| ()), as_cesu8.utf8_error());
    /// assert_eq!(Ok(()), as_cesu8.utf8_error());
    ///
    /// ```
    ///
    /// ### Invalid CESU-8, Valid UTF-8
    /// ```
    /// # use std::str::from_utf8;
    /// # use cesu8str::{Cesu8Str, Variant};
    /// const VALID_UTF8: &str = "with literal \0 null";
    /// let as_cesu8_err = Cesu8Str::from_cesu8(VALID_UTF8.as_bytes(), Variant::Java).unwrap_err();
    ///
    /// assert_eq!(std::str::from_utf8(VALID_UTF8.as_bytes()).map(|_| ()), as_cesu8_err.utf8_error());
    /// ```
    pub fn from_cesu8(bytes: &[u8], variant: Variant) -> Result<Cesu8Str<'_>, Cesu8Error> {
        // note that no 'from_cesu8_unchecked' exists, as we would have to scan the string anyway to maintain the 'utf8_err' invariant
        let utf8_err = match variant {
            Variant::Standard => decoding::cesu8_validate::<false>(bytes)?,
            Variant::Java => decoding::cesu8_validate::<true>(bytes)?,
        };

        Ok(Cesu8Str {
            variant,
            utf8_error: utf8_err,
            bytes: Cow::Borrowed(bytes),
        })
    }

    /// Creates a valid CESU-8 string, replacing invalid sequences with a replacement character.
    ///
    /// If the string is already valid, it will not allocate. Otherwise, it will allocate a new buffer.
    ///
    /// Note that if an invalid is found at the end (such as incomplete sequences), they will be replaced,
    /// even if more bytes in the buffer could fix it
    pub fn from_cesu8_lossy(bytes: &[u8], variant: Variant) -> Cesu8Str<'_> {
        let mut i = 0;
        let mut buf = Vec::new();

        // holds first UTF-8 error - in other words, first valid CESU-8
        // we are replacing otherwise invalid sequences with UTF8_REPLACEMENT_CHAR
        let mut utf8_err: Result<(), Utf8Error> = Ok(());

        while i < bytes.len() {
            // " ASCII " // Ok(s)
            // " CESU UTF4 " // Err(valid_up_to = UTF4)
            // " UTF4 CESU " // Err(valid_up_to = UTF4)
            let res = Cesu8Str::from_cesu8(&bytes[i..], variant);

            if i == 0 {
                // this is the first/only chunk
                match res {
                    Ok(s) => return s, // whole string is valid, return as-is
                    Err(_) => {
                        // pre-allocate buffer
                        assert!(buf.is_empty(), "buffer was not empty on first iteration");
                        buf = Vec::with_capacity(bytes.len());
                    }
                }
            }

            // update utf8_err invariant
            // need to mark only for valid CESU-8 sequences - any invalid UTF-8 sequences will be replaced
            match (utf8_err, &res) {
                // no other UTF-8 error, and first UTF-8 error caused by valid CESU-8
                (
                    Ok(()),
                    Ok(Cesu8Str {
                        utf8_error: Err(se),
                        ..
                    }),
                ) => {
                    utf8_err = Err(utf8err_inc(se, i));
                }

                // we found invalid UTF-8 within a valid CESU-8 chunk (and it's the first UTF-8 error)
                (
                    Ok(()),
                    Err(Cesu8Error {
                        valid_up_to,
                        utf8_error: Err(se),
                        ..
                    }),
                ) if *valid_up_to != se.valid_up_to() => utf8_err = Err(utf8err_inc(se, i)),

                (_, _) => { /* ignore if we already have a UTF-8 error, or the UTF-8 error occurs in the same spot as the CESU-8 error */
                }
            }

            match res {
                Ok(s) => {
                    // rest of the string is valid CESU-8
                    buf.extend_from_slice(s.as_bytes());

                    // since we got `Ok(_)`, this string is finished
                    // updated utf8_err above
                    return Cesu8Str {
                        variant,
                        utf8_error: utf8_err,
                        bytes: Cow::Owned(buf),
                    };
                }
                Err(e) => {
                    // push valid part of string + replacement
                    buf.extend_from_slice(&bytes[i..i + e.valid_up_to()]);
                    buf.extend_from_slice(UTF8_REPLACEMENT_CHAR);

                    match e.error_len() {
                        None => {
                            // need more bytes - we've inserted a replacement char anyway
                            return Cesu8Str {
                                variant,
                                utf8_error: utf8_err,
                                bytes: Cow::Owned(buf),
                            };
                        }
                        Some(n) => {
                            // skip past valid chunk + error
                            i += e.valid_up_to() + n;
                        }
                    }
                }
            }
        }

        Cesu8Str {
            variant,
            utf8_error: utf8_err,
            bytes: Cow::Owned(buf),
        }
    }

    /// Creates a Cesu8Str from a UTF-8 string.
    ///
    /// # Safety
    /// The internal CESU-8 string must not contain invalid CESU-8 sequences.
    ///
    /// Namely, there must not be 4-byte UTF-8 supplementary characters, and,
    /// if this is the Java variant, there must not be any nul-bytes.
    pub unsafe fn from_utf8_unchecked(bytes: Cow<'_, str>, variant: Variant) -> Cesu8Str<'_> {
        Cesu8Str {
            variant,
            utf8_error: Ok(()),
            bytes: match bytes {
                Cow::Borrowed(b) => Cow::Borrowed(b.as_bytes()),
                Cow::Owned(b) => Cow::Owned(b.into_bytes()),
            },
        }
    }

    /// Converts a UTF-8 string into a CESU-8 string, allocating if necessary.
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// # use cesu8str::{Cesu8Str, Variant};
    ///
    /// // Encode a UTF-8 str (that is also valid CESU-8) into CESU-8 without allocating
    /// let to_encode = "my string (valid CESU8)";
    /// let as_cesu8 = Cesu8Str::from_utf8(to_encode, Variant::Standard);
    /// assert!(matches!(as_cesu8.into_bytes(), Cow::Borrowed(_)));
    ///
    /// // Encode a UTF-8 str into Java CESU-8. Will allocate since it has to encode the nul byte.
    /// let to_encode_java = "my string (not valid Java CESU8)\0";
    /// let as_jcesu8 = Cesu8Str::from_utf8(to_encode_java, Variant::Java);
    /// assert!(matches!(as_jcesu8.into_bytes(), Cow::Owned(_)));
    ///
    /// // Encode an owned UTF-8 String into CESU-8. Will not allocate since the string is already owned.
    /// let to_encode = "my string (valid CESU8)".to_owned();
    /// let as_cesu8 = Cesu8Str::from_utf8(to_encode, Variant::Standard);
    /// assert!(matches!(as_cesu8.into_bytes(), Cow::Owned(_)));
    /// ```
    pub fn from_utf8<C: Into<Cow<'s, str>>>(text: C, variant: Variant) -> Cesu8Str<'s> {
        // currently always allocates, may not in the future

        let text: Cow<'s, str> = text.into();
        match encoding::utf8_as_cesu8(&text, variant) {
            Ok(()) => {
                // able to go without allocating - happy path
                Cesu8Str {
                    variant,
                    // would have returned Err(_) if there was a utf8/cesu8 incompatibility
                    utf8_error: Ok(()),
                    bytes: match text {
                        Cow::Borrowed(b) => Cow::Borrowed(b.as_bytes()),
                        Cow::Owned(v) => Cow::Owned(v.into_bytes()),
                    },
                }
            }
            Err(e) => {
                let mut data = Vec::with_capacity(default_cesu8_capacity(text.len()));

                // SAFETY: `assume_good` is valid, as we got it from a CESU-8 error above
                let res =
                    unsafe { encoding::utf8_to_cesu8(&text, e.valid_up_to(), &mut data, variant) };

                let err = res.expect("Vec io::Write has unexpectedly errored");

                Cesu8Str {
                    variant,
                    utf8_error: err,
                    bytes: Cow::Owned(data),
                }
            }
        }
    }

    /// Validates a UTF-8 string as a CESU-8 string. Will return an error if it cannot do so without allocating.
    ///
    /// See `Cesu8Str::from_utf8` for a version that will convert (and allocate if necessary)
    #[inline]
    pub fn try_from_utf8<C: Into<Cow<'s, str>>>(
        text: C,
        variant: Variant,
    ) -> Result<Cesu8Str<'s>, Cesu8Error> {
        let s = text.into();
        encoding::utf8_as_cesu8(&s, variant)
            .map(|()| {
                Cesu8Str {
                    variant,
                    bytes: match s {
                        Cow::Borrowed(s) => Cow::Borrowed(s.as_bytes()),
                        Cow::Owned(s) => Cow::Owned(s.into_bytes()),
                    },
                    // would have returned Err(_) if there was a utf8/cesu8 incompatibility
                    utf8_error: Ok(())
                }
            })
    }

    /// Creates a Cesu8Str into a provided buffer. Alternatively, the string could borrow from the original string if it is valid CESU8.
    ///
    /// May return an io::Error if there is not enough space in the provided buffer, in which case the buffer's contents is undefined.
    pub fn from_utf8_inplace(
        text: &'s str,
        buf: &'s mut [u8],
        variant: Variant,
    ) -> io::Result<Cesu8Str<'s>> {
        //eprintln!("[DEBUG] from_utf8_inplace(text = {:?}, buf.len() = {:?}, variant = {:?}", text, buf.len(), variant);
        Ok(match Cesu8Str::<'_>::try_from_utf8(text, variant) {
            Ok(c) => c, // able to go without allocating
            Err(e) => {
                let mut cursor = io::Cursor::new(buf);
                // SAFETY: `ensure_good` parameter is provided by a CESU-8 decoding error, and is thus valid
                let err = unsafe {
                    encoding::utf8_to_cesu8::<_>(text, e.valid_up_to(), &mut cursor, variant)?
                };
                let filled = cursor.position() as usize;
                let buf = cursor.into_inner();

                Cesu8Str {
                    variant,
                    utf8_error: err,
                    bytes: Cow::Borrowed(&buf[..filled]),
                }
            }
        })
    }

    /// Converts a UTF-8 string directly into the provided io::Write-capable object. This allows writing directly into a preallocated Vec or byte slice stored on the stack, for example.
    pub fn from_utf8_writer<W: io::Write>(
        text: &str,
        target: &mut W,
        variant: Variant,
    ) -> io::Result<()> {
        let () = match encoding::utf8_as_cesu8(text, variant) {
            Ok(_) => {
                // may or may not allocate depending on caller
                target.write_all(text.as_bytes())?
            }
            Err(e) => {
                let _utf8_res: Result<(), _> = unsafe {
                    // SAFETY: `ensure_good` parameter is provided by a CESU-8 decoding error, and is valid
                    encoding::utf8_to_cesu8::<W>(text, e.valid_up_to(), target, variant)?
                };
                _utf8_res.map_err(|e| io::Error::new(io::ErrorKind::Other, e))?
            }
        };
        Ok(())
    }

    /// Obtains the raw CESU8 bytes of the string
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the CESU-8 string as a UTF-8 string without allocating.
    pub fn as_str(&self) -> Result<&str, Utf8Error> {
        // borrowed -> borrowed

        self.utf8_error?; // return early if not valid utf8
        Ok(from_utf8_slice(
            &self.bytes,
            "utf8_err was not updated/set correctly",
        ))
    }

    /// Returns the CESU-8 string as a UTF-8 string, may allocate.
    pub fn to_str(&self) -> Cow<'_, str> {
        // borrowed -> borrowed
        // borrowed -> owned

        match self.utf8_error {
            Ok(()) => Cow::Borrowed(from_utf8_slice(
                &self.bytes,
                "utf8_err was not updated/set correctly",
            )),
            Err(_) => Cow::Owned(decoding::cesu8_to_utf8(self)),
        }
    }

    /// Returns the CESU-8 string as a UTF-8 string, preserving the allocation if possible.
    pub fn into_str(self) -> Cow<'s, str> {
        // owned -> owned

        if self.utf8_error.is_err() {
            // TODO: reuse allocation when re-encoding? copy bytes before first literally?
            Cow::Owned(decoding::cesu8_to_utf8(&self))
        } else {
            match self.bytes {
                // Validate UTF8 on debug, skip validation on release
                Cow::Owned(bytes) => Cow::Owned(from_utf8_vec(
                    bytes,
                    "utf8_err was not updated/set correctly",
                )),
                Cow::Borrowed(bytes) => Cow::Borrowed(from_utf8_slice(
                    bytes,
                    "utf8_err was not updated/set correctly",
                )),
            }
        }
    }

    /// Returns the underlying bytes that make up the CESU-8 string.
    pub fn into_bytes(self) -> Cow<'s, [u8]> {
        self.bytes
    }

    /// Converts between variants
    pub fn to_variant(&self, variant: Variant) -> Cesu8Str<'_> {
        if self.variant == variant {
            Cesu8Str {
                variant: self.variant,
                utf8_error: self.utf8_error,
                bytes: Cow::Borrowed(&self.bytes),
            }
        } else {
            self.clone().into_variant(variant)
        }
    }

    /// Encodes this string into the specified variant. No-op if already encoded in the variant.
    pub fn into_variant(self, variant: Variant) -> Cesu8Str<'s> {
        if self.variant == variant {
            self
        } else {
            // TODO: make this a bit more efficient?
            // can specialize this logic if it shows to be a problem

            Cesu8Str::from_utf8(self.to_str(), variant).into_owned()
        }
    }

    /// Returns a byte buffer of this CESU-8 string, converted to the specified variant with a null-terminator
    ///
    /// Allocates if there is not enough capacity to store the terminator.
    pub fn into_bytes0(self, var: Variant) -> Vec<u8> {
        let cow_bytes = self.into_variant(var).into_bytes();
        // handle cloning specially so we can allocate new string length, including null-terminator
        let mut bytes = match cow_bytes {
            Cow::Owned(o) => o,
            Cow::Borrowed(b) => {
                let mut new = Vec::with_capacity(b.len() + 1);
                new.extend_from_slice(b);
                new
            }
        };
        bytes.push(b'\0');
        bytes
    }

    /// Convenience function to turn a UTF-8 string into a null-terminated CESU-8 string of the specified variant
    pub fn reencode0<C: Into<Cow<'s, str>>>(s: C, var: Variant) -> Vec<u8> {
        Cesu8Str::from_utf8(s, var).into_bytes0(var)
    }
}

/// Returns estimated capacity needed for a byte buffer when converting UTF8 to CESU8
pub(crate) fn default_cesu8_capacity(text_len: usize) -> usize {
    text_len + (text_len >> 2)
}
