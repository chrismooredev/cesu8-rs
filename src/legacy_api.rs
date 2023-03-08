use std::borrow::Cow;

use crate::ngstr::prims::EncodingError;
use crate::{Cesu8Error, Cesu8Str, Variant, Mutf8Str};
use crate::preamble::*;

/// Convert CESU-8 data to a Rust string, re-encoding only if necessary.
/// Returns an error if the data cannot be represented as valid UTF-8.
///
/// ```
/// use std::borrow::Cow;
/// use cesu8str::from_cesu8;
///
/// // This string is valid as UTF-8 or CESU-8, so it doesn't change,
/// // and we can convert it without allocating memory.
/// assert_eq!(Cow::Borrowed("aé日"),
///            from_cesu8("aé日".as_bytes()).unwrap());
///
/// // This string is CESU-8 data containing a 6-byte surrogate pair,
/// // which becomes a 4-byte UTF-8 string.
/// let data = &[0xED, 0xA0, 0x81, 0xED, 0xB0, 0x81];
/// assert_eq!(Cow::Borrowed("\u{10401}"),
///            from_cesu8(data).unwrap());
/// ```
pub fn from_cesu8(bytes: &[u8]) -> Result<Cow<str>, Cesu8Error> {
    Cesu8Str::from_cesu8(bytes, Variant::Standard).map(|cesu| cesu.into_str())
}

/// Convert Java's modified UTF-8 data to a Rust string, re-encoding only if
/// necessary. Returns an error if the data cannot be represented as valid
/// UTF-8.
///
/// ```
/// use std::borrow::Cow;
/// use cesu8str::from_java_cesu8;
///
/// // This string is valid as UTF-8 or modified UTF-8, so it doesn't change,
/// // and we can convert it without allocating memory.
/// assert_eq!(Cow::Borrowed("aé日"),
///            from_java_cesu8("aé日".as_bytes()).unwrap());
///
/// // This string is modified UTF-8 data containing a 6-byte surrogate pair,
/// // which becomes a 4-byte UTF-8 string.
/// let data = &[0xED, 0xA0, 0x81, 0xED, 0xB0, 0x81];
/// assert_eq!(Cow::Borrowed("\u{10401}"),
///            from_java_cesu8(data).unwrap());
///
/// // This string is modified UTF-8 data containing null code-points.
/// let data = &[0xC0, 0x80, 0xC0, 0x80];
/// assert_eq!(Cow::Borrowed("\0\0"),
///            from_java_cesu8(data).unwrap());
/// ```
pub fn from_java_cesu8(bytes: &[u8]) -> Result<Cow<str>, EncodingError> {
    Mutf8Str::try_from_bytes(bytes)
        .map(|s| s.to_str())
}

#[test]
fn test_from_cesu8() {
    // The surrogate-encoded character below is from the ICU library's
    // icu/source/test/testdata/conversion.txt test case.
    let data = &[
        0x4D, 0xE6, 0x97, 0xA5, 0xED, 0xA0, 0x81, 0xED, 0xB0, 0x81, 0x7F,
    ];
    assert_eq!(
        Cow::Borrowed("M日\u{10401}\u{7F}"),
        from_cesu8(data).unwrap()
    );

    // We used to have test data from the CESU-8 specification, but when we
    // worked it through manually, we got the wrong answer:
    //
    // Input: [0xED, 0xAE, 0x80, 0xED, 0xB0, 0x80]
    // Binary: 11101101 10101110 10000000 11101101 10110000 10000000
    //
    // 0b1101_101110_000000 -> 0xDB80
    // 0b1101_110000_000000 -> 0xDC00
    //
    // ((0xDB80 - 0xD800) << 10) | (0xDC00 - 0xDC00) -> 0xE0000
    // 0x10000 + 0xE0000 -> 0xF0000
    //
    // The spec claims that we are supposed to get 0x10000, not 0xF0000.
    // Since I can't reconcile this example data with the text of the
    // specification, I decided to use a test character from ICU instead.
}

/// Convert a Rust `&str` to CESU-8 bytes.
///
/// ```
/// use std::borrow::Cow;
/// use cesu8str::to_cesu8;
///
/// // This string is valid as UTF-8 or CESU-8, so it doesn't change,
/// // and we can convert it without allocating memory.
/// assert_eq!(Cow::Borrowed("aé日".as_bytes()), to_cesu8("aé日"));
///
/// // This string is a 4-byte UTF-8 string, which becomes a 6-byte CESU-8
/// // vector.
/// assert_eq!(Cow::Borrowed(&[0xED, 0xA0, 0x81, 0xED, 0xB0, 0x81]),
///            to_cesu8("\u{10401}"));
/// ```
pub fn to_cesu8(text: &str) -> Cow<[u8]> {
    Cesu8Str::from_utf8(text, Variant::Standard).bytes
}

/// Convert a Rust `&str` to Java's modified UTF-8 bytes.
///
/// ```
/// use std::borrow::Cow;
/// use cesu8str::to_java_cesu8;
///
/// // This string is valid as UTF-8 or CESU-8, so it doesn't change,
/// // and we can convert it without allocating memory.
/// assert_eq!(Cow::Borrowed("aé日".as_bytes()), to_java_cesu8("aé日"));
///
/// // This string is a 4-byte UTF-8 string, which becomes a 6-byte modified
/// // UTF-8 vector.
/// assert_eq!(Cow::Borrowed(&[0xED, 0xA0, 0x81, 0xED, 0xB0, 0x81]),
///            to_java_cesu8("\u{10401}"));
///
/// // This string contains null, which becomes 2-byte modified UTF-8 encoding
/// assert_eq!(Cow::Borrowed(&[0xC0, 0x80, 0xC0, 0x80]),
///            to_java_cesu8("\0\0"));
/// ```
pub fn to_java_cesu8(text: &str) -> Cow<[u8]> {
    match Mutf8Str::from_utf8(text) {
        Cow::Borrowed(b) => Cow::Borrowed(b.as_bytes()),
        Cow::Owned(o) => Cow::Owned(o.into_bytes())
    }
}

/// Check whether a Rust string contains valid CESU-8 data.
pub fn is_valid_cesu8(text: &str) -> bool {
    Cesu8Str::try_from_utf8(text, Variant::Standard).is_ok()
}

/// Check whether a Rust string contains valid Java's modified UTF-8 data.
pub fn is_valid_java_cesu8(text: &str) -> bool {
    Mutf8Str::try_from_utf8(text).is_ok()
}

#[test]
fn test_valid_cesu8() {
    assert!(is_valid_cesu8("aé日"));
    assert!(is_valid_java_cesu8("aé日"));
    assert!(!is_valid_cesu8("\u{10401}"));
    assert!(!is_valid_java_cesu8("\u{10401}"));
    assert!(is_valid_cesu8("\0\0"));
    assert!(!is_valid_java_cesu8("\0\0"));
}
