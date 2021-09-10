use std::borrow::Cow;
use std::io;
use std::str::Utf8Error;

use crate::encoding;
use crate::decoding;
use crate::Cesu8DecodingError;
#[cfg(test)] use crate::encoding::enc_surrogates;

// TODO: turn JAVA into a Variant ?
/// A CESU-8 string
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Cesu8Str<'s, const JAVA: bool> {
    /// If the data within `self.bytes` is also valid UTF-8
    pub(crate) utf8_err: Result<(), Utf8Error>,

    /// The contained string data. If modified, `self.is_utf8` must be updated.
    pub(crate) bytes: Cow<'s, [u8]>,
}

impl<'s, const JAVA: bool> Cesu8Str<'s, JAVA> {
    /// Clones the string's data to produce an owned version.
    pub fn into_owned(self) -> Cesu8Str<'static, JAVA> {
        let owned: Vec<u8> = match self.bytes {
            Cow::Borrowed(s) => s.to_owned(),
            Cow::Owned(v) => v,
        };
        Cesu8Str {
            utf8_err: self.utf8_err,
            bytes: Cow::Owned(owned),
        }
    }
    
    /// Validates a sequence of bytes as CESU8
    pub fn from_cesu8<C: Into<Cow<'s, [u8]>>>(bytes: C) -> Result<Cesu8Str<'s, JAVA>, Cesu8DecodingError> {
        // note that no 'from_cesu8_unchecked' exists, as we would have to scan the string anyway to maintain the 'utf8_err' invariant

        decoding::cesu8_validate(bytes.into())
    }

    /// Creates a Cesu8Str from a UTF-8 string.
    ///
    /// # Safety
    /// The internal CESU-8 string must not contain invalid CESU-8 sequences.
    ///
    /// Namely, there must not be 4-byte UTF-8 supplementary characters, and,
    /// if this is the Java variant, there must not be any nul-bytes.
    pub unsafe fn from_utf8_unchecked(bytes: Cow<'_, str>) -> Cesu8Str<'_, JAVA> {
        Cesu8Str {
            utf8_err: Ok(()),
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
    /// # use cesu8::Cesu8Str;
    /// 
    /// // Encode a UTF-8 str (that is also valid CESU-8) into CESU-8 without allocating
    /// let to_encode = "my string (valid CESU8)";
    /// let as_cesu8 = Cesu8Str::<false>::from_utf8(to_encode);
    /// assert!(matches!(as_cesu8.into_bytes(), Cow::Borrowed(_)));
    /// 
    /// // Encode a UTF-8 str into Java CESU-8. Will allocate since it has to encode the nul byte.
    /// let to_encode_java = "my string (not valid Java CESU8)\0";
    /// let as_jcesu8 = Cesu8Str::<true>::from_utf8(to_encode_java);
    /// assert!(matches!(as_jcesu8.into_bytes(), Cow::Owned(_)));
    /// 
    /// // Encode an owned UTF-8 String into CESU-8. Will not allocate since the string is already owned.
    /// let to_encode = "my string (valid CESU8)".to_owned();
    /// let as_cesu8 = Cesu8Str::<false>::from_utf8(to_encode);
    /// assert!(matches!(as_cesu8.into_bytes(), Cow::Owned(_)));
    /// ```
    pub fn from_utf8<C: Into<Cow<'s, str>>>(text: C) -> Cesu8Str<'s, JAVA> {
        // currently always allocates, may not in the future

        let text = text.into();

        match encoding::utf8_as_cesu8::<JAVA>(Cow::Borrowed(&text)) {
            Ok(c) => { // able to go without allocating
                Cesu8Str {
                    utf8_err: c.utf8_err,
                    bytes: match text {
                        Cow::Borrowed(b) => Cow::Borrowed(b.as_bytes()),
                        Cow::Owned(v) => Cow::Owned(v.into_bytes()),
                    }
                }
            }, 
            Err(e) => {
                let mut data = Vec::with_capacity(default_cesu8_capacity(text.len()));

                // SAFETY: `assume_good` is valid, as we got it from a CESU-8 error above
                let res = unsafe { encoding::utf8_to_cesu8_prealloc::<_, JAVA>(&text, e.valid_up_to(), &mut data) };

                let err = res.expect("Vec io::Write has unexpectedly errored");

                Cesu8Str {
                    utf8_err: err,
                    bytes: Cow::Owned(data),
                }
            }
        }
    }

    /// Validates a UTF-8 string as a CESU-8 string. Will return an error if it cannot do so without allocating.
    ///
    /// See `Cesu8Str::from_utf8` for a version that will convert (and allocate if necessary)
    pub fn try_from_utf8<C: Into<Cow<'s, str>>>(text: C) -> Result<Cesu8Str<'s, JAVA>, Cesu8DecodingError> {
        encoding::utf8_as_cesu8(text.into())
    }

    /// Creates a Cesu8Str into a provided buffer. Alternatively, the string could borrow from the original string if it is valid CESU8.
    ///
    /// May return an io::Error if there is not enough space in the provided buffer, in which case the buffer's contents is undefined.
    pub fn from_utf8_inplace(text: &'s str, buf: &'s mut [u8]) -> io::Result<Cesu8Str<'s, JAVA>> {
        Ok(match Cesu8Str::<'_, JAVA>::try_from_utf8(text) {
            Ok(c) => c, // able to go without allocating
            Err(e) => {
                let mut cursor = io::Cursor::new(buf);
                // SAFETY: `ensure_good` parameter is provided by a CESU-8 decoding error, and is thus valid
                let err = unsafe { encoding::utf8_to_cesu8_prealloc::<_, JAVA>(text, e.valid_up_to(), &mut cursor)? };
                let filled = cursor.position() as usize;
                let buf = cursor.into_inner();

                Cesu8Str {
                    utf8_err: err,
                    bytes: Cow::Borrowed(&buf[..filled]),
                }
            }
        })
    }

    /// Converts a UTF-8 string directly into the provided io::Write-capable object.
    pub fn from_utf8_writer<W: io::Write>(text: &str, target: &mut W) -> io::Result<()> {
        let () = match Cesu8Str::<'_, JAVA>::try_from_utf8(text) {
            Ok(_) => {
                // may or may not allocate depending on caller
                target.write_all(text.as_bytes())?
            },
            Err(e) => {
                // SAFETY: `ensure_good` parameter is provided by a CESU-8 decoding error, and is valid
                let _utf8_err = unsafe { encoding::utf8_to_cesu8_prealloc::<W, JAVA>(text, e.valid_up_to(), target)? };
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

        if cfg!(debug_assertions) {
            let res = std::str::from_utf8(&self.bytes);
            assert_eq!(res.map(|_| ()), self.utf8_err, "utf8_err was not updated/set correctly");
            res
        } else {
            let () = self.utf8_err?;
            Ok(unsafe { std::str::from_utf8_unchecked(&self.bytes) })
        }
    }

    /// Returns the CESU-8 string as a UTF-8 string, allocating only if necessary
    pub fn to_str(&self) -> Cow<'_, str> {
        // borrowed -> borrowed
        // borrowed -> owned
        
        match self.utf8_err {
            Ok(()) if cfg!(debug_assertions) => Cow::Borrowed(std::str::from_utf8(&self.bytes).expect("utf8_err was not updated/set correctly")),
            Ok(()) => Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(&self.bytes) }),
            
            Err(_) => Cow::Owned(decoding::cesu8_to_utf8(self)),
        }
    }

    /// Returns the CESU-8 string as a UTF-8 string, preserving the allocation if possible.
    pub fn into_str(self) -> Cow<'s, str> {
        // owned -> owned

        if self.utf8_err.is_err() {
            // TODO: reuse allocation when re-encoding? copy bytes before first literally?
            Cow::Owned(decoding::cesu8_to_utf8(&self))
        } else {
            match self.bytes {
                // Validate UTF8 on debug, skip validation on release
                Cow::Owned(bytes) if cfg!(debug_assertions) => Cow::Owned(String::from_utf8(bytes).expect("utf8_err was not updated/set correctly")),
                Cow::Borrowed(bytes) if cfg!(debug_assertions) => Cow::Borrowed(std::str::from_utf8(bytes).expect("utf8_err was not updated/set correctly")),
                Cow::Owned(bytes) => Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) }),
                Cow::Borrowed(bytes) => Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(bytes) }),
            }
        }
    }

    /// Returns the underlying bytes that make up the CESU-8 string.
    pub fn into_bytes(self) -> Cow<'s, [u8]> {
        self.bytes
    }
}

/// Returns estimated capacity needed for a byte buffer when converting UTF8 to CESU8
pub(crate) fn default_cesu8_capacity(text_len: usize) -> usize {
    text_len + (text_len >> 2)
}

// impl Add<Cesu8Str> for Cesu8Str
// impl Add<str> for Cesu8Str
// impl AddAssign<Cesu8Str> for Cesu8Str
// impl AddAssign<str> for Cesu8Str

#[cfg(test)]
fn test_encoded<const JAVA: bool>(text: &str, expected: &[u8]) {
    let variant = if JAVA { "Java" } else { "Standard" };

    let cesu8 = Cesu8Str::<JAVA>::from_utf8(text);
    assert_eq!(expected, cesu8.as_bytes(), "[{} variant][{:?}] unable to properly encode to CESU-8", variant, text);
    let utf8_err = std::str::from_utf8(expected).map(|_| ());
    assert_eq!(utf8_err, cesu8.utf8_err, "[{} variant][{:?}] utf8_err invariant was not maintained (CESU-8 bytes: {:x?})", variant, text, cesu8.as_bytes());

    let utf8 = cesu8.to_str();
    assert_eq!(text, utf8, "[{} variant][{:?}] unexpected decoding from CESU-8 to UTF-8", variant, text)
}
#[cfg(test)]
fn test_encoded_same(text: &str, expected: &[u8]) {
    test_encoded::<false>(text, expected);
    test_encoded::<true>(text, expected);
}

#[cfg(test)]
fn test_surrogates(ch: char, expected: &[u8; 6]) {
    let encoded = encoding::enc_surrogates(ch);
    assert_eq!(expected, &encoded, "enc_surrogates returned unexpected encoded character");

    let decoded = decoding::dec_surrogates(encoded[1], encoded[2], encoded[4], encoded[5]);
    let decoded_ch = std::str::from_utf8(&decoded).expect("dec_surrogates returned invalid UTF-8")
        .chars().next().unwrap();

    assert_eq!(ch, decoded_ch, "dec_surrogates returned unexpected character");
}

#[test]
fn surrogates() {
    test_surrogates('🟣', b"\xED\xA0\xBD\xED\xBF\xA3");
}

#[test]
fn embedded_nuls() {
    test_encoded::<false>("plain", b"plain");
    test_encoded::<false>("start\0end", b"start\0end");
    test_encoded::<false>("\0middle\0", b"\0middle\0");
    test_encoded::<false>("\0\0\0", b"\0\0\0");

    test_encoded::<true>("plain", b"plain");
    test_encoded::<true>("start\0end", b"start\xC0\x80end");
    test_encoded::<true>("\0middle\0", b"\xC0\x80middle\xC0\x80");
    test_encoded::<true>("\0\0\0", b"\xC0\x80\xC0\x80\xC0\x80");
}

#[test]
fn supplementary_pairs() {
    // TODO: refactor these to use concat_bytes! if/when implemented/stablized
    // TODO: Use a variety of different characters? (though all 4-byte chars should be handled exactly the same)
    assert_eq!("🟣".len(), 4);
    assert_eq!("🟣".as_bytes(), b"\xf0\x9f\x9f\xa3");
    assert_eq!(&enc_surrogates('🟣'), b"\xED\xA0\xBD\xED\xBF\xA3");

    test_encoded_same("plain", b"plain");
    test_encoded_same("start🟣end", b"start\xED\xA0\xBD\xED\xBF\xA3end");
    test_encoded_same("🟣middle🟣", b"\xED\xA0\xBD\xED\xBF\xA3middle\xED\xA0\xBD\xED\xBF\xA3");
    test_encoded_same("🟣🟣🟣", b"\xED\xA0\xBD\xED\xBF\xA3\xED\xA0\xBD\xED\xBF\xA3\xED\xA0\xBD\xED\xBF\xA3");
}

#[test]
fn from_utf8_inplace() {
    let text = "hello\0";
    
    // reuse string
    {
        // buffer shouldn't even be used - leave it at length 0
        let mut buf = [0; 0];
        let std = Cesu8Str::<false>::from_utf8_inplace(text, &mut buf).expect("string to be literal, no io necessary");
        
        // if borrowed, it comes from the `text` as `buf` is zero-length
        assert!(matches!(std.bytes, Cow::Borrowed(_)), "did not use str data for Cesu8Str");
    }

    // use buffer
    {
        // buffer shouldn't even be used - leave it at length 0
        let mut buf = [0; 16];
        let std = Cesu8Str::<true>::from_utf8_inplace(text, &mut buf).expect("there was not enough space in buf");
        
        // if borrowed, it comes from the `buf` as `text` would have to change
        assert!(matches!(std.bytes, Cow::Borrowed(_)), "did not use str data for Cesu8Str");
        assert_eq!(std.bytes.len(), 7, "string length was not as expected");
    }

    // not enough space
    {
        // buffer shouldn't even be used - leave it at length 0
        let mut buf = [0; 0];
        let res = Cesu8Str::<true>::from_utf8_inplace(text, &mut buf);

        assert!(res.is_err(), "there was enough space in buf, with 0-length buf");
    }
}

