
use std::borrow::Cow;
use std::io;
use std::str::Utf8Error;

use crate::Variant;
use crate::{Cesu8Error, TAG_CONT_U8};
use crate::string::Cesu8Str;
use crate::unicode::utf8_char_width;

/// Validates UTF-8 string as CESU-8, erroring if any non-CESU-8 sequences are found.
pub(crate) fn utf8_as_cesu8_spec<const ENCODE_NUL: bool>(text: Cow<'_, str>) -> Result<Cesu8Str<'_>, Cesu8Error> {
    let mut i = 0;
    let text_bytes = match text {
        Cow::Borrowed(b) => Cow::Borrowed(b.as_bytes()),
        Cow::Owned(b) => Cow::Owned(b.into_bytes()),
    };
    while i < text_bytes.len() {
        // eprintln!("[{}:{}, encode_nul = {}] i = {}, slice = {:?}, whole = {:?}", file!(), line!(), ENCODE_NUL, i, &text_bytes[i..], &text_bytes);
        let b = text_bytes[i];
        if ENCODE_NUL && b == b'\0' {
            return Err(Cesu8Error::new(i, Some(1), Ok(())));
        }

        // ascii fast-path
        if b.is_ascii() {
            i += 1;
            continue;
        }

        let w = utf8_char_width(b);

        // if width = 4 then we'd have to re-encode
        if w == 4 {
            // str is always valid UTF8, so there was enough characters, and there was exactly four of them (not None)
            return Err(Cesu8Error::new(i, Some(4), Ok(())));
        }

        // skip the continuation bytes of the character
        // this should always be at least 1 for valid UTF8, which &str provides
        assert_ne!(w, 0, "utf8 char length was 0, this is illegal in well-formed utf8 strings (byte {:x?}, bytes[{}] from {:x?})", b, i, text_bytes);
        i += w;
    }

    Ok(Cesu8Str {
        variant: ENCODE_NUL.into(),
        utf8_error: Ok(()),
        bytes: text_bytes,
    })
}

#[inline]
pub(crate) fn utf8_as_cesu8(text: Cow<'_, str>, variant: Variant) -> Result<Cesu8Str<'_>, Cesu8Error> {
    match variant {
        Variant::Standard => utf8_as_cesu8_spec::<false>(text),
        Variant::Java => utf8_as_cesu8_spec::<true>(text),
    }
}

/// Re-encodes UTF-8 bytes as CESU-8, returning the first created Utf8Error
///
/// Depends on the caller to provide a writable object of appropriate size, and to cast the written bytes to a Cesu8Str
///
/// # Safety
/// `assume_good` should be an index into `text`, where all the bytes within `&text[..assume_good]` are valid CESU-8.
///
/// As this range will be written to `encoded` literally, and not checked, then providing a range with invalid CESU-8 may result in undefined behavior.
///
/// A value of `0` for `assume_good` will always be safe.
pub(crate) unsafe fn utf8_to_cesu8_spec<W: io::Write, const ENCODE_NUL: bool>(text: &str, assume_good: usize, encoded: &mut W) -> io::Result<Result<(), Utf8Error>> {
    
    // make an internal function so unsafe parts can still be checked
    if assume_good != 0 {
        // check that this is correct on debug builds
        debug_assert_eq!(utf8_as_cesu8_spec::<ENCODE_NUL>(Cow::Borrowed(text)).unwrap_err().valid_up_to(), assume_good, "tried to assume invalid CESU-8 as good");
        debug_assert!(assume_good <= text.len(), "tried to assume_good a chunk larger than the source");
    }

    #[inline(always)]
    fn utf8_to_cesu8_prealloc_internal<W: io::Write, const ENCODE_NUL: bool>(text: &str, assume_good: usize, encoded: &mut W) -> io::Result<Result<(), Utf8Error>> {
        let bytes = text.as_bytes();

        encoded.write_all(&bytes[..assume_good])?;

        // start after we've already decoded some bits
        
        // index into `text`
        let mut i = assume_good;
        let mut utf8_seg = 0;
        let mut utf8_err = Ok(());

        // how much we've written to 'encoded', for a utf8_err index if necessary
        let mut written = assume_good;

        macro_rules! write_cesu8 {
            ($cesu8_slice: expr, $text_len: expr) => {
                let sl: &[u8] = $cesu8_slice;
                encoded.write_all(sl)?;
                written += sl.len();
                i += $text_len;
            }
        }

        macro_rules! push_utf8 {
            ($errlen: expr) => {
                if utf8_seg > 0 {
                    // push utf8_segment
                    write_cesu8!(&bytes[i..i+utf8_seg], utf8_seg);

                    utf8_seg = 0;
                }

                // update utf8_err if this is the first error
                if let Some(err) = $errlen {
                    if utf8_err.is_ok() {
                        utf8_err = Err(utf8err_new(written, err));
                    }
                }
            }
        }

        // while i+utf8_seg < bytes.len() {
        while let Some(&b) = bytes.get(i+utf8_seg) {
            // let b = bytes[i+utf8_seg];
            if ENCODE_NUL && b == b'\0' {
                push_utf8!(Some(Some(1))); // injected 0xC0,0x80 will be invalid UTF-8

                // re-encode nul, skip it
                write_cesu8!(&[0xC0, 0x80], 1);
            } else if b.is_ascii() { // ascii range
                utf8_seg += 1;
            } else {
                match utf8_char_width(b) {
                    4 => {
                        push_utf8!(Some(Some(1)));

                        // re-encode character, skip it
                        let s = unsafe { std::str::from_utf8_unchecked(&bytes[i..i+4]) };
                        let c = s.chars().next().unwrap() as u32;

                        write_cesu8!(&enc_surrogates(c), 4);
                    },
                    w => {
                        // w should only be in range 1..=3
                        utf8_seg += w;
                    }
                }
            }
        }

        push_utf8!(None);

        // more to prevent unused_assignment warnings in push_utf8 macro than anything
        debug_assert_eq!(i, text.len(), "did not fully consume the input text bytes");
        debug_assert_eq!(utf8_seg, 0, "did not fully consume the current utf8 segment");

        Ok(utf8_err)
    }

    utf8_to_cesu8_prealloc_internal::<W, ENCODE_NUL>(text, assume_good, encoded)
}

#[inline]
pub(crate) unsafe fn utf8_to_cesu8<W: io::Write>(text: &str, assume_good: usize, encoded: &mut W, variant: Variant) -> io::Result<Result<(), Utf8Error>> {
    match variant {
        Variant::Standard => utf8_to_cesu8_spec::<W, false>(text, assume_good, encoded),
        Variant::Java => utf8_to_cesu8_spec::<W, true>(text, assume_good, encoded),
    }
}


#[inline]
pub(crate) fn enc_surrogates<C: Into<u32>>(ch: C) -> [u8; 6] {
    // encode `ch` into a supplementary UTF-16 pair (`high` and `low`), then convert the raw pair data to (invalid) UTF-8

    let c = ch.into() - 0x10000;
    let high  = enc_surrogate(((c >> 10) as u16)   | 0xD800);
    let low = enc_surrogate(((c & 0x3FF) as u16) | 0xDC00);

    [
        high[0], high[1], high[2],
        low[0], low[1], low[2],
    ]
}

/// Encode a single surrogate as CESU-8.
#[inline]
fn enc_surrogate(surrogate: u16) -> [u8; 3] {
    debug_assert!((0xD800..=0xDFFF).contains(&surrogate), "trying to encode invalid surrogate pair");
    // 1110xxxx 10xxxxxx 10xxxxxx
    [0b11100000  | ((surrogate & 0b1111_0000_0000_0000) >> 12) as u8,
     TAG_CONT_U8 | ((surrogate & 0b0000_1111_1100_0000) >>  6) as u8,
     TAG_CONT_U8 |  (surrogate & 0b0000_0000_0011_1111)        as u8]
}

/// There is no way to create a Utf8Error outside the stdlibrary, so unsafely artifically create one
///
/// This is useful for marking a specific index/length as a UTF8Error without performing O(n) string validation through stdlib
#[inline]
pub(crate) fn utf8err_new(valid_up_to: usize, err_len: Option<u8>) -> Utf8Error {
    #[allow(dead_code)]
    struct CustomUtf8Error {
        valid_up_to: usize,
        err_len: Option<u8>,
    }

    let err = CustomUtf8Error {
        valid_up_to,
        err_len,
    };

    // (loosly) ensure that Utf8Error does not change
    debug_assert_eq!(std::mem::align_of::<CustomUtf8Error>(), std::mem::align_of::<Utf8Error>(), "std::str::Utf8Error has unexpectedly changed alignment");
    debug_assert_eq!(std::mem::size_of::<CustomUtf8Error>(), std::mem::size_of::<Utf8Error>(), "std::str::Utf8Error has unexpectedly changed alignment");

    unsafe { std::mem::transmute(err) }
}

#[inline]
pub(crate) fn utf8err_inc(err: &Utf8Error, incby: usize) -> Utf8Error {
    utf8err_new(incby + err.valid_up_to(), err.error_len().map(|b| b as u8))
}
