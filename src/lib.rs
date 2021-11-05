// Copyright 2012-2014 The Rust Project Developers and Eric Kidd.  See the
// COPYRIGHT-RUST.txt file at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.


//! A simple library implementing the [CESU-8 compatibility encoding
//! scheme](http://www.unicode.org/reports/tr26/tr26-2.html).  This is a
//! non-standard variant of UTF-8 that is used internally by some systems
//! that need to represent UTF-16 data as 8-bit characters.  Yes, this is
//! ugly.
//!
//! Use of this encoding is discouraged by the Unicode Consortium.  It's OK
//! for working with existing internal APIs, but it should not be used for
//! transmitting or storing data.
//!
//! ```
//! use std::borrow::Cow;
//! use cesu8::{from_cesu8, to_cesu8};
//!
//! // 16-bit Unicode characters are the same in UTF-8 and CESU-8.
//! assert_eq!(Cow::Borrowed("aé日".as_bytes()),
//!            to_cesu8("aé日"));
//! assert_eq!(Cow::Borrowed("aé日"),
//!            from_cesu8("aé日".as_bytes()).unwrap());
//!
//! // This string is CESU-8 data containing a 6-byte surrogate pair,
//! // which decodes to a 4-byte UTF-8 string.
//! let data = &[0xED, 0xA0, 0x81, 0xED, 0xB0, 0x81];
//! assert_eq!(Cow::Borrowed("\u{10401}"),
//!            from_cesu8(data).unwrap());
//! ```
//!
//! ### A note about security
//!
//! As a general rule, this library is intended to fail on malformed or
//! unexpected input.  CESU-8 is supposed to be an internal-only format,
//! and if we're seeing malformed data, we assume that it's either a bug in
//! somebody's code, or an attacker is trying to improperly encode data to
//! evade security checks.
//!
//! If you have a use case for lossy conversion to UTF-8, or conversion
//! from mixed UTF-8/CESU-8 data, please feel free to submit a pull request
//! for `from_cesu8_lossy_permissive` with appropriate behavior.
//!
//! ### Java and U+0000, and other variants
//!
//! Java uses the CESU-8 encoding as described above, but with one
//! difference: The null character U+0000 is represented as an overlong
//! UTF-8 sequence `C0 80`. This is supported by the `from_java_cesu8` and
//! `to_java_cesu8` methods.
//!
//! ### Surrogate pairs and UTF-8
//!
//! The UTF-16 encoding uses "surrogate pairs" to represent Unicode code
//! points in the range from U+10000 to U+10FFFF.  These are 16-bit numbers
//! in the range 0xD800 to 0xDFFF.
//!
//! * 0xD800 to 0xDBFF: First half of surrogate pair.  When encoded as
//!   CESU-8, these become **1110**1101 **10**100000 **10**000000 to
//!   **1110**1101 **10**101111 **10**111111.
//!
//! * 0xDC00 to 0xDFFF: Second half of surrogate pair.  These become
//!   **1110**1101 **10**110000 **10**000000 to
//!   **1110**1101 **10**111111 **10**111111.
//!
//! Wikipedia [explains](http://en.wikipedia.org/wiki/UTF-16) the
//! code point to UTF-16 conversion process:
//!
//! > Consider the encoding of U+10437 (𐐷):
//! >
//! > * Subtract 0x10000 from 0x10437. The result is 0x00437, 0000 0000 0100
//! >   0011 0111.
//! > * Split this into the high 10-bit value and the low 10-bit value:
//! >   0000000001 and 0000110111.
//! > * Add 0xD800 to the high value to form the high surrogate: 0xD800 +
//! >   0x0001 = 0xD801.
//! > * Add 0xDC00 to the low value to form the low surrogate: 0xDC00 +
//! >   0x0037 = 0xDC37.

#![warn(missing_docs)]

mod unicode;
mod string;
mod string_impls;
mod decoding;
mod encoding;
mod legacy_api;

pub use crate::string::Cesu8Str;
pub use crate::decoding::Cesu8Error;
pub use crate::legacy_api::*;

/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111u8;
/// Value of the tag bits (tag mask is !CONT_MASK) of a continuation byte.
const TAG_CONT_U8: u8 = 0b1000_0000u8;

/// Which variant of the encoding are we working with?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variant {
    /// Regular CESU-8, with '\0' represented as itself.
    Standard,

    /// This is technically Java's "Modified UTF-8", which is supposedly
    /// like CESU-8, except that it UTF-8 encodes the '\0' byte.  I'm sure
    /// it seemed like a good idea at the time.
    Java,
}

impl Variant {
    /// Returns true if this Variant of CESU-8 converts nul-bytes to a `&[0xC0, 0x80]` sequence.
    ///
    /// This should only be true for the Java variant of CESU-8, also known as Modified UTF-8.
    pub const fn encodes_nul(&self) -> bool {
        match self {
            Variant::Standard => false,
            Variant::Java => true,
        }
    }
}

// Currently using a const generic bool for specializing functions for each variant
// once const_generics is stabalized, we can use the variant directly
// Creations of Cesu8Str should use this impl, then this impl can be removed once
// const_generics is stabalized and we can adjust things properly
#[doc(hidden)]
impl From<bool> for Variant {
    fn from(b: bool) -> Variant {
        match b {
            false => Variant::Standard,
            true => Variant::Java,
        }
    }
}
