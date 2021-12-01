use std::borrow::{Borrow};
use std::fmt;
use std::ops::{Add, AddAssign};
use std::hash::{Hash, Hasher};
use crate::{Cesu8Str, Variant};
use crate::encoding::utf8err_inc;

/// Used for equality/hashing across variants so bytes will be the same
const COMMON_VARIANT: Variant = Variant::Standard;


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

impl<'s> Eq for Cesu8Str<'s> {}
impl<'s> PartialEq<Cesu8Str<'_>> for Cesu8Str<'s> {
    fn eq(&self, other: &Cesu8Str<'_>) -> bool {
        if self.variant == other.variant {
            self.bytes == other.bytes
        } else {
            let left = self.to_variant(COMMON_VARIANT);
            let right = other.to_variant(COMMON_VARIANT);
            left.bytes == right.bytes
        }
    }
}
impl<'s> PartialEq<str> for Cesu8Str<'s> {
    fn eq(&self, other: &str) -> bool {
        self.to_str() == other
    }
}

// can't implement things like (&str -> Cesu8Str) since we don't know the desired Variant

impl From<Cesu8Str<'_>> for String {
    fn from(c8s: Cesu8Str) -> String {
        c8s.to_str().into_owned()
    }
}
impl From<Cesu8Str<'_>> for Vec<u8> {
    fn from(c8s: Cesu8Str) -> Vec<u8> {
        c8s.bytes.into_owned()
    }
}

impl<'s> AsRef<[u8]> for Cesu8Str<'s> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}
impl<'s> Borrow<[u8]> for Cesu8Str<'s> {
    fn borrow(&self) -> &[u8] {
        self.as_bytes()
    }
}

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

impl<'s> fmt::Display for Cesu8Str<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // implicit conversion to UTF-8
        f.write_str(&self.to_str())
    }
}
// impl Default -- Nope, would need variant
// impl Ord
impl Hash for Cesu8Str<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // to ensure `k1 == k2 -> hash(k1) == hash(k2)` holds,
        // we need to turn this into a common variant as a
        // sort of lingua-franca between our two variants
        // (otherwise bytes could differ for logically same string)
        self.to_variant(COMMON_VARIANT).bytes.hash(state);
    }
}

// allow mutable operations ala str? (eg: basically just ASCII upper/lower case conversions)
