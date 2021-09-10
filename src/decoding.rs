use std::borrow::Cow;
use std::error::Error;
use std::fmt;

use crate::CONT_MASK;
use crate::TAG_CONT_U8;
use crate::encoding::utf8_as_cesu8;
use crate::string::Cesu8Str;

// TODO: lift out the allocation, write to a provided Write instance (Cursor<Vec<u8>> -> String for example)

/// Errors which can occur when attempting to interpret a `str` or sequence
/// of `u8` as a CESU8 string.
///
/// # Examples
///
/// This error type’s methods can be used to create functionality
/// similar to `String::from_utf8_lossy` without allocating heap memory:
///
/// ```
/// todo!("make this CESU8 applicable");
/// fn from_utf8_lossy<F>(mut input: &[u8], mut push: F) where F: FnMut(&str) {
///     loop {
///         match std::str::from_utf8(input) {
///             Ok(valid) => {
///                 push(valid);
///                 break
///             }
///             Err(error) => {
///                 let (valid, after_valid) = input.split_at(error.valid_up_to());
///                 unsafe {
///                     push(std::str::from_utf8_unchecked(valid))
///                 }
///                 push("\u{FFFD}");
///
///                 if let Some(invalid_sequence_length) = error.error_len() {
///                     input = &after_valid[invalid_sequence_length..]
///                 } else {
///                     break
///                 }
///             }
///         }
///     }
/// }
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cesu8DecodingError {
    valid_up_to: usize,
    error_len: Option<u8>,
}
impl Error for Cesu8DecodingError {
    fn description(&self) -> &str { "decoding error" }
    fn cause(&self) -> Option<&dyn Error> { None }
}

impl fmt::Display for Cesu8DecodingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "could not convert CESU-8 data to UTF-8")
    }
}
impl Cesu8DecodingError {
    pub(crate) fn new(valid_up_to: usize, error_len: Option<usize>) -> Cesu8DecodingError {
        Cesu8DecodingError {
            valid_up_to,
            error_len: error_len.map(|l| l as u8)
        }
    }

    /// Creates a new Cesu8DecodingError struct, with `beginning` added to it's `valid_up_to` field.
    ///
    /// This will generally only be used for better error reporting. (such as in streams where data may be handled in chunks)
    pub fn increase_valid_index(&self, beginning: usize) -> Cesu8DecodingError {
        Cesu8DecodingError {
            valid_up_to: self.valid_up_to + beginning,
            error_len: self.error_len,
        }
    }

    /// Returns the index in the given string up to which valid CESU-8 was
    /// verified.
    ///
    /// It is the maximum index such that `Variant::from_cesu8(&input[..index])`
    /// would return `Ok(_)`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// todo!("convert this to a CESU8 applicable example");
    /// use std::str;
    ///
    /// // some invalid bytes, in a vector
    /// let sparkle_heart = vec![0, 159, 146, 150];
    ///
    /// // std::str::from_utf8 returns a Utf8Error
    /// let error = str::from_utf8(&sparkle_heart).unwrap_err();
    ///
    /// // the second byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```
    #[inline]
    pub fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }

    /// Provides more information about the failure:
    ///
    /// * `None`: the end of the input was reached unexpectedly.
    ///   `self.valid_up_to()` is 1 to 3 bytes from the end of the input.
    ///   If a byte stream (such as a file or a network socket) is being decoded incrementally,
    ///   this could be a valid `char` whose CESU-8 byte sequence is spanning multiple chunks.
    ///
    /// * `Some(len)`: an unexpected byte was encountered.
    ///   The length provided is that of the invalid byte sequence
    ///   that starts at the index given by `valid_up_to()`.
    ///   Decoding should resume after that sequence
    ///   (after inserting a [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD]) in case of
    ///   lossy decoding.
    ///
    /// [U+FFFD]: std::char::REPLACEMENT_CHARACTER
    #[inline]
    pub fn error_len(&self) -> Option<usize> {
        self.error_len.map(|n| n as usize)
    }
}

/// Decodes a valid CESU8 bytestring into a UTF8 string. Always allocates, always validates.
pub(crate) fn cesu8_to_utf8<const JAVA: bool>(cesu: &Cesu8Str<'_, JAVA>) -> String {
    // note that we can take advantage of the fact that the input should be well-formed CESU8

    let bytes = cesu.as_bytes();
    
    // try to copy initial N bytes first
    let (mut i, mut dest) = match cesu.utf8_err {
        Ok(()) => {
            // cesu is valid UTF8 - copy into new String literally
            let as_vec = cesu.bytes.to_vec();

            // SAFETY: our bytes have already been checked as valid UTF-8
            return unsafe { String::from_utf8_unchecked(as_vec) };
        },
        Err(utf8_err) => {
            let valid_up_to = utf8_err.valid_up_to();
            
            // SAFETY: bytes up to valid_up_to have already been validated as UTF-8
            let mut dest = unsafe { String::from_utf8_unchecked(cesu.bytes[..valid_up_to].to_vec()) };
            dest.reserve(cesu.bytes.len() - valid_up_to);
            (valid_up_to, dest)
        }
    };

    // let mut dest = String::with_capacity(bytes.len() + (bytes.len() / 4));

    while i < bytes.len() {
        // Try to use fast stdlib from_utf8 except where it is invalid
        // luckily the 4-byte chars as 6-byte sequences are invalid, and so are the 0xC0,0x80 sequences that Java uses
        match std::str::from_utf8(&bytes[i..]) {
            // The rest of the string is valid, append + return
            Ok(s) => {
                // could re-use the allocation if i == 0 and we are passed an owned version
                dest += s;
                return dest;
            },

            // We have reached an invalid character. For valid CESU8, this should be a supplementary character surrogate pair, or for Java's CESU8, a null character.
            Err(e) => {
                let valid_up_to = e.valid_up_to();

                // SAFETY: we have previously validated this portion already
                dest += unsafe { std::str::from_utf8_unchecked(&bytes[i..i+valid_up_to]) };
                debug_assert!(e.error_len().is_some(), "reached unterminated sequence, this should be impossible for validated CESU8");
                i += valid_up_to;

                let rest = &bytes[i..];
                // debug_assert!(rest.len() > 0, "found no bytes while e.error_len().is_none()");
                
                // found either 6-pair, or (if JAVA) a 0xC0,0x80 sequence
                if JAVA && rest.starts_with(&[0xC0, 0x80]) {
                    dest.push('\0');
                    i += 2;
                } else if let Some(&[first, second, third, fourth, fifth, sixth]) = rest.get(..6) {
                    debug_assert!(first == 0xED && fourth == 0xED, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);

                    // from_utf8 should consume any valid three-bytes sequences
                    // our three-byte surrogate pairs should be invalid, and caught here

                    // assert our continuation bytes are indeed continuations
                    // assert our second & fifth bytes are on the right side of each other

                    debug_assert!((second & !CONT_MASK) == TAG_CONT_U8);
                    debug_assert!((second & 0b1111_0000) == 0b1010_0000);
                    debug_assert!((third & !CONT_MASK) == TAG_CONT_U8);

                    debug_assert!((fifth & !CONT_MASK) == TAG_CONT_U8);
                    debug_assert!((fifth & 0b1111_0000) == 0b1011_0000);
                    debug_assert!((sixth & !CONT_MASK) == TAG_CONT_U8);
                    
                    let utf8bytes: [u8; 4] = dec_surrogates(second, third, fifth, sixth);

                    dest.push_str(if cfg!(debug_assertions) {
                        std::str::from_utf8(&utf8bytes).expect("dec_surrogates did not return valid UTF8")
                    } else {
                        // SAFETY: dec_surrogates should always return valid UTF-8
                        unsafe { std::str::from_utf8_unchecked(&utf8bytes) }
                    });
                    i += 6;
                } else {
                    unreachable!("unknown CESU8 decoding error. Was a Cesu8Str made with invalid CESU-8 bytes? (next 6 bytes: {:x?})", &rest[..6]);
                }
            },
        }
    }
    
    debug_assert!(i == bytes.len());
    dest
}

/// Validates raw bytes as CESU8, reporting any errors if found. Will not allocate.
pub(crate) fn cesu8_validate<const JAVA: bool>(bytes: Cow<'_, [u8]>) -> Result<Cesu8Str<'_, JAVA>, Cesu8DecodingError> {
    let mut i = 0;
    let mut first_utf8_err = None;

    // attempt to validate strings as UTF8 first, then validate each UTF8 segment as CESU8 individually

    // TODO: implement own UTF8 checking so this can be O(N) instead of O(2N)
    // copy ascii literally, only check for UTF8 when not ascii bytes found?

    while i < bytes.len() {
        let from_utf8 = std::str::from_utf8(&bytes[i..]);

        // get valid string portion
        let utf8 = match from_utf8 {
            Ok(s) => s,
            Err(e) => unsafe { std::str::from_utf8_unchecked(&bytes[i..i+e.valid_up_to()]) }
        };

        // test that for CESU8 validity, report CESU8 errors in the validated UTF8
        let cesu8: Cesu8Str<JAVA> = utf8_as_cesu8(Cow::Borrowed(utf8))
            // return err if it is not valid
            .map_err(|e| e.increase_valid_index(i))?;

        // if we validated all of it, we stop
        let cesu8_validated_len = cesu8.as_bytes().len();
        if i + cesu8_validated_len == bytes.len() {
            i += cesu8_validated_len;
            break;
        }

        // if we did not consume the whole thing, there should have been a UTF8 error
        let e = from_utf8.unwrap_err();
        if first_utf8_err.is_none() {
            first_utf8_err = Some(e);
        }

        // otherwise we determine if we can handle the UTF8 error

        // if there was not enough data, error out
        if e.error_len().is_none() {
            return Err(Cesu8DecodingError::new(i + e.valid_up_to(), None));
        }

        // there was enough data - check for bytes as CESU8 instead of UTF8
        let rest = &bytes[i+cesu8_validated_len..];

        if rest.len() < 2 {
            return Err(Cesu8DecodingError::new(i + e.valid_up_to(), e.error_len()));
        }

        // check for Java embedded null
        if JAVA && rest[0] == 0xC0 && rest[1] == 0x80 {
            // It's an embedded null-byte - it is valid
            i += cesu8_validated_len + 2;
            continue;
        }

        // from_utf8 should consume any valid three-bytes sequences
        // our three-byte surrogate pairs should be invalid, and caught here

        // assert our continuation bytes are indeed continuations
        // assert our second & fifth bytes are on the right side of each other
        if rest[0] == 0xED && rest[3] == 0xED && rest.len() >= 6
            && (rest[1] & !CONT_MASK) == TAG_CONT_U8
            && (rest[1] & 0b1111_0000) == 0b1010_0000 // first half
            && (rest[2] & !CONT_MASK) == TAG_CONT_U8
            && (rest[4] & !CONT_MASK) == TAG_CONT_U8
            && (rest[4] & 0b1111_0000) == 0b1011_0000 // second half
            && (rest[5] & !CONT_MASK) == TAG_CONT_U8
        {
            // surrogate halves - it is valid
            i += cesu8_validated_len + 6;
            continue;
        }

        return Err(Cesu8DecodingError::new(i + e.valid_up_to(), e.error_len()));
    }

    debug_assert_eq!(i, bytes.len(), "read more or less bytes than total");

    Ok(Cesu8Str {
        utf8_err: first_utf8_err.map_or(Ok(()), Err),
        bytes,
    })
}


/// Convert the two trailing bytes from a CESU-8 surrogate to a regular
/// surrogate value.
fn dec_surrogate(second: u8, third: u8) -> u32 {
    0xD000u32 | ((second & CONT_MASK) as u32) << 6 | (third & CONT_MASK) as u32
}

/// Convert the bytes from a CESU-8 surrogate pair into a valid UTF-8
/// sequence.  Assumes input is valid.
pub(crate) fn dec_surrogates(second: u8, third: u8, fifth: u8, sixth: u8) -> [u8; 4] {
    // Convert to a 32-bit code point.
    let s1 = dec_surrogate(second, third);
    let s2 = dec_surrogate(fifth, sixth);
    let c = 0x10000 + (((s1 - 0xD800) << 10) | (s2 - 0xDC00));
    //println!("{:0>8b} {:0>8b} {:0>8b} -> {:0>16b}", 0xEDu8, second, third, s1);
    //println!("{:0>8b} {:0>8b} {:0>8b} -> {:0>16b}", 0xEDu8, fifth, sixth, s2);
    //println!("-> {:0>32b}", c);
    assert!((0x010000..=0x10FFFF).contains(&c));

    // Convert to UTF-8.
    // 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    [0b1111_0000u8 | ((c & 0b1_1100_0000_0000_0000_0000) >> 18) as u8,
     TAG_CONT_U8   | ((c & 0b0_0011_1111_0000_0000_0000) >> 12) as u8,
     TAG_CONT_U8   | ((c & 0b0_0000_0000_1111_1100_0000) >>  6) as u8,
     TAG_CONT_U8   |  (c & 0b0_0000_0000_0000_0011_1111)        as u8]
}

#[test]
fn cesu8_sequences_are_invalid_utf8() {
    // These should always be held correct, as it is what makes CESU-8 different to UTF-8

    // b"CESU8" // "UTF8"
    const WITH_SURROGATE: &[u8] = b"surrogate\xED\xA0\xBD\xED\xBF\xA3pair"; // "surrogate🟣pair"
    const WITH_NUL: &[u8] = b"my\xC0\x80string"; // "my\0string"

    assert!(std::str::from_utf8(WITH_SURROGATE).is_err());
    assert!(std::str::from_utf8(WITH_NUL).is_err());
}

