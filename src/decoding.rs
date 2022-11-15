use std::borrow::Cow;
use std::error::Error;
use std::fmt;
use std::num::NonZeroUsize;
use std::str::Utf8Error;

use crate::Variant;
use crate::encoding::utf8_as_cesu8_spec;
use crate::encoding::utf8err_inc;
use crate::encoding::utf8err_new;
use crate::string::Cesu8Str;


/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111u8;
/// Value of the tag bits (tag mask is !CONT_MASK) of a continuation byte.
pub(crate) const TAG_CONT_U8: u8 = 0b1000_0000u8;

/// Errors which can occur when attempting to interpret a `str` or sequence
/// of `u8` as a CESU8 string.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cesu8Error {
    /// `bytes[..valid_up_to]` is a valid CESU-8 string
    pub(crate) valid_up_to: usize,
    
    /// should resume CESU-8 for `bytes[valid_up_to+error_len.unwrap()]`
    /// 
    /// If None, more data is needed
    pub(crate) error_len: Option<NonZeroUsize>,

    /// Any UTF-8 errors that would have occured within the CESU-8 slice
    pub(crate) utf8_error: Result<(), Utf8Error>,
}
impl Error for Cesu8Error {
    fn description(&self) -> &str { "decoding error" }
    fn cause(&self) -> Option<&dyn Error> { None }
}

impl fmt::Display for Cesu8Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "could not convert CESU-8 data to UTF-8")
    }
}
impl Cesu8Error {
    #[inline] // inline to hopefully take out the .expect if constants are passed (or numbers verifyably over zero)
    pub(crate) fn new(valid_up_to: usize, error_len: Option<usize>, utf8_error: Result<(), Utf8Error>) -> Cesu8Error {
        Cesu8Error {
            valid_up_to,
            error_len: error_len.map(|el| NonZeroUsize::new(el).expect("attempted to create zero-size endoing error")),
            utf8_error,
        }
    }
    pub(crate) fn with_utf8_error(&self, err: Result<(), Utf8Error>) -> Cesu8Error {
        let mut cesuerr = *self;
        cesuerr.utf8_error = err;
        cesuerr
    }

    /// Creates a new Cesu8DecodingError struct, with `beginning` added to it's `valid_up_to` field.
    ///
    /// This will generally only be used for better error reporting. (such as in streams where data may be handled in chunks)
    pub fn increase_valid_index(&self, beginning: usize) -> Cesu8Error {
        Cesu8Error {
            valid_up_to: self.valid_up_to + beginning,
            error_len: self.error_len,
            utf8_error: self.utf8_error.map_err(|e| utf8err_new(e.valid_up_to() + beginning, e.error_len().map(|u| u as u8))),
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
    /// use cesu8str::{Cesu8Str, Variant};
    ///
    /// // some invalid bytes, in a byte string
    /// // the '\xC0' is the first half to an embedded Java-style nul sequence
    /// let sparkle_heart: &[u8] = b"my \xC0 string";
    ///
    /// // cesu8str::Cesu8Str::from_cesu8 returns a Cesu8Error
    /// let error = Cesu8Str::from_cesu8(&sparkle_heart, Variant::Java).unwrap_err();
    ///
    /// // the third byte is invalid here, the error is 1 byte long
    /// assert_eq!(3, error.valid_up_to());
    /// assert_eq!(Some(1), error.error_len());
    /// ```
    #[inline]
    pub fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }

    /// Provides more information about the failure:
    ///
    /// * `None`: the end of the input was reached unexpectedly.
    ///   If a byte stream (such as a file or a network socket) is being decoded incrementally,
    ///   this could be a valid `char` whose CESU-8 byte sequence is spanning multiple chunks.
    ///
    /// * `Some(len)`: an unexpected byte or byte sequence was encountered.
    ///   The length provided is that of the invalid byte sequence
    ///   that starts at the index given by `valid_up_to()`.
    ///   Decoding should resume after that sequence
    ///   (after inserting a [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD]) in case of
    ///   lossy decoding.
    ///
    ///   Note that `Cesu8DecodingError::error_len` differs from `Utf8Error::error_len` in that
    ///   the cesu8 version reports the length until the next valid UTF-8 sequence (or end of string)
    ///   while the utf8 version often reports each erroring byte individually.
    ///
    /// [U+FFFD]: std::char::REPLACEMENT_CHARACTER
    #[inline]
    pub fn error_len(&self) -> Option<usize> {
        self.error_len.map(|nzus| nzus.get())
    }

    /// Access an underlying UTF-8 error that may have occured before this CESU-8 error.
    /// If this returns `Ok(())` then it can be assumed that the source slice is valid CESU-8 and UTF-8 up to `self.valid_up_to()`
    /// 
    /// If a UTF-8 error would occur at the same index as this CESU-8 error, and they both need more data, this should be `Ok(())`. In other words, `error_len() == None` can also be considered an implicit UTF-8 error.
    #[inline]
    pub fn utf8_error(&self) -> Result<(), Utf8Error> {
        self.utf8_error
    }
}

/// Decodes a valid CESU8 bytestring into a UTF8 string. Always allocates, always validates.
pub(crate) fn cesu8_to_utf8_const<const ENCODE_NUL: bool>(cesu: &Cesu8Str<'_>) -> String {
    // note that we can take advantage of the fact that the input should be well-formed CESU8
    debug_assert_eq!(Variant::from(ENCODE_NUL), cesu.variant, "ran wrong const-generic routine for cesu type");
    debug_assert!(cesu8_validate::<ENCODE_NUL>(&cesu.bytes).is_ok(), "stored invalid CESU-8 within Cesu8Str (cesu8 str: variant={:?}, utf8_err={:?}, bytes={:X?})", cesu.variant, cesu.utf8_error, cesu.bytes);

    let bytes = cesu.as_bytes();
    
    // try to copy initial N bytes first
    let (mut i, mut dest) = match cesu.utf8_error {
        Ok(()) => {
            // cesu is valid UTF8 - copy into new String literally
            let as_vec = cesu.bytes.to_vec();

            // SAFETY: our bytes have already been checked as valid UTF-8
            return from_utf8_vec(as_vec, "invalid UTF8 is in a CESU-8 string without UTF-8 errors");
        },
        Err(utf8_err) => {
            let valid_up_to = utf8_err.valid_up_to();
            
            // SAFETY: bytes up to valid_up_to have already been validated as UTF-8
            let mut dest = from_utf8_slice(&cesu.bytes[..valid_up_to], "invalid UTF8 is in a CESU-8 string before the recorded UTF-8 error").to_owned();
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
                debug_assert!(!rest.is_empty(), "found no bytes to consume without consuming whole string");
                
                // found either 6-pair, or (if JAVA) a 0xC0,0x80 sequence
                if ENCODE_NUL && rest.starts_with(&[0xC0, 0x80]) {
                    dest.push('\0');
                    i += 2;
                } else if let Some(&[first, second, third, fourth, fifth, sixth]) = rest.get(..6) {
                    debug_assert!(first == 0xED && fourth == 0xED, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);

                    // from_utf8 should consume any valid three-bytes sequences
                    // our three-byte surrogate pairs should be invalid, and caught here

                    // assert our continuation bytes are indeed continuations
                    // assert our second & fifth bytes are on the right side of each other

                    debug_assert!((second & !CONT_MASK) == TAG_CONT_U8, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);
                    debug_assert!((second & 0b1111_0000) == 0b1010_0000, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);
                    debug_assert!((third & !CONT_MASK) == TAG_CONT_U8, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);

                    debug_assert!((fifth & !CONT_MASK) == TAG_CONT_U8, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);
                    debug_assert!((fifth & 0b1111_0000) == 0b1011_0000, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);
                    debug_assert!((sixth & !CONT_MASK) == TAG_CONT_U8, "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})", &rest[..6]);
                    
                    let utf8bytes: [u8; 4] = dec_surrogates(second, third, fifth, sixth);

                    dest.push_str(from_utf8_slice(&utf8bytes, "dec_surrogates did not return valid UTF8"));
                    i += 6;
                } else {
                    unreachable!("unknown CESU8 decoding error. Was a Cesu8Str made with invalid CESU-8 bytes? (next (i={})..6 bytes: {:x?}) (cesu8 str: {:x?})", i, &rest[..6.min(rest.len())], bytes);
                }
            },
        }
    }
    
    debug_assert_eq!(bytes.len(), i, "did not consume expected number of bytes while converting cesu8 to utf8");
    dest
}

pub(crate) fn cesu8_to_utf8(cesu: &Cesu8Str<'_>) -> String {
    match cesu.variant {
        Variant::Standard => cesu8_to_utf8_const::<false>(cesu),
        Variant::Java => cesu8_to_utf8_const::<true>(cesu),
    }
}


/// Validates raw bytes as CESU8, reporting any errors if found. Will not allocate.
pub(crate) fn cesu8_validate<const ENCODE_NUL: bool>(bytes: &[u8]) -> Result<Result<(), Utf8Error>, Cesu8Error> {
    let mut i = 0;
    let mut first_utf8_error: Result<(), Utf8Error> = Ok(());
    // let mut current_utf8_error: Option<Utf8Error> = None;

    while i < bytes.len() {
        let try_utf8 = std::str::from_utf8(&bytes[i..])
            .map_err(|uerr| utf8err_inc(&uerr, i));
        
        // update first_utf8_error
        if let Err(uerr) = &try_utf8 {
            if first_utf8_error.is_ok() {
                first_utf8_error = Err(*uerr);
            }
        }

        let try_cesu8: Result<Cesu8Str, Cesu8Error> = {
            let s = try_utf8.unwrap_or_else(|uerr| unsafe { std::str::from_utf8_unchecked(&bytes[i..uerr.valid_up_to()]) });

            utf8_as_cesu8_spec::<ENCODE_NUL>(Cow::Borrowed(s))
                .map_err(|e| e.increase_valid_index(i))
        };
        

        // This should either return, or explicitly `continue`
        // It doesn't matter what type this is, as long as it's not `()`
        match (try_utf8, try_cesu8) {
            (Ok(_), Ok(c)) => {
                // valid UTF-8/CESU-8 -> consumed rest of string
                i += c.bytes.len();
                debug_assert_eq!(i, bytes.len(), "found valid UTF-8 & CESU-8 that did not consume rest of string");
                return Ok(first_utf8_error);
            },
            (Ok(_) | Err(_), Err(cerr)) => {
                // recieved a chunk of valid UTF-8, which contained a CESU-8 error

                // the CESU-8 error should be prioritized, so return that

                return Err(cerr.with_utf8_error(first_utf8_error));
            },
            (Err(uerr), Ok(c)) => {
                // UTF-8 error, but we have a valid CESU-8 chunk from the valid UTF-8 portion
                debug_assert_eq!(uerr.valid_up_to(), i+c.bytes.len(), "CESU-8 string valid with unexpected length");
                i += c.bytes.len();
                
                // need to process a new UTF-8 error
                // may simply be that we need more data
                fn validate_byte<F: FnOnce(u8) -> bool>(bytes: &[u8], start: usize, offset: usize, first_utf8_error: Result<(), Utf8Error>, check: F) -> Result<(), Cesu8Error> {
                    match bytes.get(start+offset) {
                        None => Err(Cesu8Error::new(start, None, first_utf8_error)),
                        Some(b) if check(*b) => Ok(()),
                        Some(_) => Err(until_next_codepoint(bytes, start, first_utf8_error)),
                    }
                }

                if uerr.error_len().is_none() {
                    return Err(Cesu8Error::new(i, None, first_utf8_error));
                }

                debug_assert!(i+1 < bytes.len(), "there were no more bytes after a UTF-8 error with a length");
                // eprintln!("[{}:{}] reading CESU-8 specific sequence at index {} or 0x{:X} (total len = {}) (assert_cesu = {}) (next 8 bytes: {:X?})", file!(), line!(), i, i, bytes.len(), first_cesu, &bytes[i..(i+8).min(bytes.len())]);
                
                // do not try to loop this - there are valid UTF-8 sequences starting with 0xED that we could falsely try to interpret as CESU-8
                match bytes[i] {
                    0xC0 if ENCODE_NUL => {
                        validate_byte(bytes, i, 1, first_utf8_error, |b| b == 0x80)?;
                        i += 2;
                    },
                    0xED => {
                        // from_utf8 should consume any valid three-bytes sequences
                        // our three-byte surrogate pairs should be invalid, and caught here

                        // assert our continuation bytes are indeed continuations
                        // assert our second & fifth bytes are on the right side of each other

                        // note that the way that validate_byte works, if there is an error in the first half,
                        // then the error length only accounts for the first half. An unpaired second half will be emitted
                        // as a separate error

                        // could split these up, but these have to occur in pairs - if they don't, it's invalid
                        validate_byte(bytes, i, 1, first_utf8_error, |b| b & !CONT_MASK == TAG_CONT_U8)?;
                        validate_byte(bytes, i, 1, first_utf8_error, |b| b & 0b1111_0000 == 0b1010_0000)?; // first half
                        validate_byte(bytes, i, 2, first_utf8_error, |b| b & !CONT_MASK == TAG_CONT_U8)?;

                        validate_byte(bytes, i, 3, first_utf8_error, |b| b == 0xED)?;
                        validate_byte(bytes, i, 4, first_utf8_error, |b| b & !CONT_MASK == TAG_CONT_U8)?;
                        validate_byte(bytes, i, 4, first_utf8_error, |b| b & 0b1111_0000 == 0b1011_0000)?; // second half
                        validate_byte(bytes, i, 5, first_utf8_error, |b| b & !CONT_MASK == TAG_CONT_U8)?;
                        i += 6;
                    },
                    _ => {
                        // not valid UTF-8 or CESU-8
                        // eprintln!("[{}:{}] returning err of next codepoint (i..len={:?}, bytes[i..len] = {:x?})", file!(), line!(), i..bytes.len(), &bytes[i..bytes.len()]);
                        debug_assert!(std::str::from_utf8(&bytes[i..]).is_err(), "could be solved with more data, but thats not is reported");
                        return Err(until_next_codepoint(bytes, i, first_utf8_error));
                    },
                }

                continue;
            },
        }
    }

    assert_eq!(bytes.len(), i, "did not error, but reached end without consuming entire byte slice (expected {}, processed {})", bytes.len(), i);
    Ok(first_utf8_error)
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
    assert!((0x010000..=0x10FFFF).contains(&c), "attempt to decode invalid cesu-8 6-byte surrogate pair");
    
    // Convert to UTF-8.
    // 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    [0b1111_0000u8 | ((c & 0b1_1100_0000_0000_0000_0000) >> 18) as u8,
     TAG_CONT_U8   | ((c & 0b0_0011_1111_0000_0000_0000) >> 12) as u8,
     TAG_CONT_U8   | ((c & 0b0_0000_0000_1111_1100_0000) >>  6) as u8,
     TAG_CONT_U8   |  (c & 0b0_0000_0000_0000_0011_1111)        as u8]
}

/// Given a byte buffer and a byte index, returns a Cesu8DecodingError that
/// states `&bytes[..start]` is valid, and that the error lasts until the
/// start of the next ascii character, UTF-8 codepoint, or the end of the string.
fn until_next_codepoint(bytes: &[u8], start: usize, utf8_err: Result<(), Utf8Error>) -> Cesu8Error {
    // TODO: should semantics of this return None if there is no next valid character/UTF-8 codepoint?
    // eg: return error_len() == None if we haven't found valid data
    let skip = bytes.iter().copied()
        .skip(start+1) // skip start byte of error
        .take_while(|b| b & !CONT_MASK == TAG_CONT_U8) // while we are in a continuation byte
        .count() + 1; // +1 for skipped start byte
    // TODO: rework the semantics so we can do a whole error? change error_len to usize?
    assert!(start+skip < bytes.len(), "next valid index may be after chunk - need more data?");
    Cesu8Error::new(start, Some(skip), utf8_err)
}

#[inline] #[track_caller]
pub(crate) fn from_utf8_slice<'s>(by: &'s [u8], expect_msg: &'_ str) -> &'s str {
    if cfg!(debug_assertions) {
        std::str::from_utf8(by).expect(expect_msg)
    } else {
        unsafe { std::str::from_utf8_unchecked(by) }
    }
}
#[inline] #[track_caller]
pub(crate) fn from_utf8_vec(by: Vec<u8>, expect_msg: &str) -> String {
    if cfg!(debug_assertions) {
        String::from_utf8(by).expect(expect_msg)
    } else {
        unsafe { String::from_utf8_unchecked(by) }
    }
}

#[test]
fn next_codepoint() {
    assert_eq!(1, until_next_codepoint(b"++\xC0\x80++", 0, Ok(())).error_len().unwrap());
    assert_eq!(2, until_next_codepoint(b"++\xC0\x80++", 2, Ok(())).error_len().unwrap());
    assert_eq!(1, until_next_codepoint(b"++\xC0\x80++", 4, Ok(())).error_len().unwrap());
}
#[test] #[should_panic]
fn next_codepoint_past_slice_length() {
    // should panic as it should skip 'past' the end of the string
    until_next_codepoint(b"++\xC0\x80++", 6, Ok(()));
}

#[test]
fn next_codepoint_embedded_nul() {
    const BYTES: &[u8] = b"A \xC0\x80 ";
    let dummy_utf8_err = utf8err_new(2, Some(1));
    let err_with_skip = until_next_codepoint(BYTES, 2, Err(dummy_utf8_err));
    assert_eq!(Cesu8Error::new(2, Some(2), Err(dummy_utf8_err)), err_with_skip);
}

#[test]
fn cesu8_sequences_are_invalid_utf8() {
    use crate::encoding::utf8err_new;
    // These should always be held correct, as it is what makes CESU-8 different to UTF-8

    // b"CESU8" // "UTF8"
    const WITH_SURROGATE: &[u8] = b"surrogate\xED\xA0\xBD\xED\xBF\xA3pair"; // "surrogate🟣pair"
    const WITH_NUL: &[u8] = b"my\xC0\x80string"; // "my\0string"

    assert_eq!(std::str::from_utf8(WITH_SURROGATE), Err(utf8err_new(9, Some(1))));
    assert_eq!(std::str::from_utf8(WITH_NUL), Err(utf8err_new(2, Some(1))));
}

#[test]
fn utf8_error_len_is_propagated() {
    // we have valid CESU-8, followed by invalid (cut-short) UTF-8
    // 0xE6 starts a 3-byte UTF-8 sequence that is cut short
    const TEST_DATA: &[u8] = b"\xED\xA4\xB8\xED\xB1\xA0\xE6\x82";

    let err = Cesu8Str::from_cesu8(TEST_DATA, Variant::Standard)
        .expect_err("unterminated 3-byte UTF-8 sequence should cause CESU-8 error");
    
    // proper CESU-8 error should report we need more data to finish the sequence
    assert_eq!(None, err.error_len(), "should need more data to finish 3-byte UTF-8 sequence");
    assert_eq!(6, err.valid_up_to(), "CESU-8 error should be valid until unterminated UTF-8");

    // actual UTF-8 error should report the first UTF-8 error in the string - the first one
    let utf8_err = err.utf8_error().expect_err("invalid UTF-8 should set utf8_error");
    assert_eq!(Some(1), utf8_err.error_len(), "CESU-8 surrogate pair should be invalid UTF-8");
    assert_eq!(0, utf8_err.valid_up_to(), "CESU-8 surrogate pair should be invalid UTF-8");

    // test proper string internal assertions are still held
    let valid = Cesu8Str::from_cesu8(&TEST_DATA[..err.valid_up_to()], Variant::Standard)
        .expect("removing invalid portion should result in valid CESU-8");
    let utf8_err_valid = valid.utf8_error().expect_err("invalid UTF-8 should set utf8_error");
    assert_eq!(Some(1), utf8_err_valid.error_len(), "CESU-8 surrogate pair should be invalid UTF-8");
    assert_eq!(0, utf8_err_valid.valid_up_to(), "CESU-8 surrogate pair should be invalid UTF-8");
}

#[test]
fn utf8_error_len_is_propagated_separated() {
    // we have valid CESU-8, followed by invalid (cut-short) UTF-8
    // 0xE6 starts a 3-byte UTF-8 sequence that is cut short
    // adding a space to exercise different code paths
    const TEST_DATA: &[u8] = b"\xED\xA4\xB8\xED\xB1\xA0 \xE6\x82";

    let err = Cesu8Str::from_cesu8(TEST_DATA, Variant::Standard)
        .expect_err("unterminated 3-byte UTF-8 sequence should cause CESU-8 error");
    
    // proper CESU-8 error should report we need more data to finish the sequence
    assert_eq!(None, err.error_len(), "should need more data to finish 3-byte UTF-8 sequence");
    assert_eq!(7, err.valid_up_to(), "CESU-8 error should be valid until unterminated UTF-8");

    // actual UTF-8 error should report the first UTF-8 error in the string - the first one
    let utf8_err = err.utf8_error().expect_err("invalid UTF-8 should set utf8_error");
    assert_eq!(Some(1), utf8_err.error_len(), "CESU-8 surrogate pair should be invalid UTF-8");
    assert_eq!(0, utf8_err.valid_up_to(), "CESU-8 surrogate pair should be invalid UTF-8");

    // test proper string internal assertions are still held
    let valid = Cesu8Str::from_cesu8(&TEST_DATA[..err.valid_up_to()], Variant::Standard)
        .expect("removing invalid portion should result in valid CESU-8");
    let utf8_err_valid = valid.utf8_error().expect_err("invalid UTF-8 should set utf8_error");
    assert_eq!(Some(1), utf8_err_valid.error_len(), "CESU-8 surrogate pair should be invalid UTF-8");
    assert_eq!(0, utf8_err_valid.valid_up_to(), "CESU-8 surrogate pair should be invalid UTF-8");
}

#[test]
fn non_cesu_ed() {
    // test that valid 3-byte UTF-8 sequences starting with '0xED' are still recognized as valid UTF-8,
    // even when between CESU-8 sequences starting with 0xED

    // let bytes = b"\xed\x8d\xad";
    // last three bytes are valid UTF-8, first 6 are CESU-8 surrogate pair
    let bytes = b"\xed\xa3\xbc\xed\xbe\x97\xed\x85\xae";
    // let as_str = std::str::from_utf8(bytes).unwrap();
    
    // let _ = Cesu8Str::from_utf8(as_str, Variant::Standard);
    let _ = Cesu8Str::from_cesu8(bytes, Variant::Standard).unwrap();
}