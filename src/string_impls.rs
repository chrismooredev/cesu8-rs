use std::fmt;
use std::ops::{Add, AddAssign};
use crate::Cesu8Str;
use crate::encoding::utf8err_inc;


impl<'cs, 'us> Add<&'us Cesu8Str<'us>> for Cesu8Str<'cs> {
    type Output = Cesu8Str<'cs>;
    fn add(mut self, text: &'us Cesu8Str<'us>) -> Self::Output {
        self.add_assign(text);
        self
    }
}
impl<'cs, 'us> Add<&'us str> for Cesu8Str<'cs> {
    type Output = Cesu8Str<'cs>;

    fn add(mut self, text: &'us str) -> Self::Output {
        self.add_assign(text);
        self
    }
}
impl<'cs, 'us> AddAssign<&'us Cesu8Str<'us>> for Cesu8Str<'cs> {
    fn add_assign(&mut self, rhs: &'us Cesu8Str<'us>) {
        let old_len = self.bytes.len();
        
        let text = rhs.to_variant(self.variant);
        self.bytes.to_mut().extend_from_slice(text.as_bytes());

        match (self.utf8_error, text.utf8_error) {
            (Err(_), _) => { /* There is a UTF-8 error before appending the other string, ignore */ }
            (Ok(()), Ok(())) => { /* Both are valid UTF-8, no need to change cached error */ },
            (Ok(()), Err(e)) => {
                self.utf8_error = Err(utf8err_inc(&e, old_len));
            },
        }
    }
}
impl<'cs, 'us> AddAssign<&'us str> for Cesu8Str<'cs> {
    fn add_assign(&mut self, text: &'us str) {
        let old_len = self.bytes.len();
        let bytes: &mut Vec<u8> = self.bytes.to_mut();

        match crate::encoding::utf8_to_cesu8_safe(text, bytes, self.variant) {
            Ok(()) => { /* Introduced no UTF-8 errors, leave error as is */ },
            Err(e) if self.utf8_error.is_ok() => {
                // There was an error in our new chunk, none in our own
                self.utf8_error = Err(utf8err_inc(&e, old_len));
            },
            Err(_) => { /* Introduced a UTF-8 error, but one preceded it, so this one is irrelavent */ }
        }
    }
}
// impl std::fmt::Write ??

// impl From<&str> for Cesu8Str
// impl From<Cesu8Str> for String
// impl From<Cesu8Str> for CString
// impl From<Cesu8Str> for Vec<u8> // CString::new(cesu8str)
// impl AsRef<&[u8]> for Cesu8Str
// impl Borrow<[u8]> for Cesu8Str

// impl Debug (to not show all bytes as hex - escape invalid utf8 as hex?)
impl<'s> fmt::Debug for Cesu8Str<'s> {
    /// Display a debug representation of the string, escaping non-ascii characters to hex
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // could use from_utf8_unchecked here safely
        let pretty = String::from_utf8(
            self.bytes.iter().copied()
                // leaves ascii as is, uses \t, \n, or \xNN as fallback for unknown/unicode
                .flat_map(std::ascii::escape_default)
                .collect()
        ).expect("flat_map output did not return stringable text");

        struct DisplayToDebug<T: fmt::Display>(T);
        impl<T: fmt::Display> fmt::Debug for DisplayToDebug<T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        f.debug_struct("Cesu8Str")
            .field("variant", &self.variant)
            .field("first_utf8_error", &self.utf8_error)
            .field("bytes", &DisplayToDebug(pretty))
            .finish()
    }
}
// impl Display (implicit conversion to UTF-8, show that)
impl<'s> fmt::Display for Cesu8Str<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_str())
    }
}
// impl Default
// impl Eq, Hash, Ord
// Index
// PartialEq<u8, Cow<str | [u8]>, Cesu8Str, String, OsStr, OsString>

// allow mutable operations ala str? (eg: basically just ASCII upper/lower case conversions)
