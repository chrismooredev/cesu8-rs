
use crate::Cesu8Error;
use crate::prelude::*;

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
    Cesu8Str::try_from_bytes(bytes)
        .map(|cesu| cesu.to_str())
        .map_err(|ee| Cesu8Error {
            valid_up_to: ee.valid_up_to(),
            error_len: ee.error_len().map(|nzu8| nzu8.into()),
            utf8_error: std::str::from_utf8(bytes).map(|_| ())
        })
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
pub fn from_java_cesu8(bytes: &[u8]) -> Result<Cow<str>, Cesu8Error> {
    Mutf8Str::try_from_bytes(bytes)
        .map(|cesu| cesu.to_str())
        .map_err(|ee| Cesu8Error {
            valid_up_to: ee.valid_up_to(),
            error_len: ee.error_len().map(|nzu8| nzu8.into()),
            utf8_error: std::str::from_utf8(bytes).map(|_| ())
        })
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
    match Cesu8Str::from_utf8(text) {
        Cow::Borrowed(b) => Cow::Borrowed(b.as_bytes()),
        Cow::Owned(o) => Cow::Owned(o.into_bytes()),
    }
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
    Cesu8Str::try_from_utf8(text).is_ok()
}

/// Check whether a Rust string contains valid Java's modified UTF-8 data.
pub fn is_valid_java_cesu8(text: &str) -> bool {
    Mutf8Str::try_from_utf8(text).is_ok()
}
