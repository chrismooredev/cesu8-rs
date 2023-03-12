

use std::error::Error;
use std::fmt;
use std::num::NonZeroU8;
use std::num::NonZeroUsize;
use std::simd::*;
use std::io;
use std::borrow::Cow;
use std::convert::TryInto;

// use crate::decoding::{dec_surrogates, TAG_CONT_U8, CONT_MASK};

pub const DEFAULT_CHUNK: usize = 64;

/// Mask of the value bits of a continuation byte.
pub(crate) const CONT_MASK: u8 = 0b0011_1111u8;
/// Value of the tag bits (tag mask is !CONT_MASK) of a continuation byte.
pub(crate) const TAG_CONT_U8: u8 = 0b1000_0000u8;

const TAG_LEN4_MASK: u8 = 0b1111_1000;
const TAG_LEN4_VAL: u8  = 0b1111_0000;

pub(crate) const MUTF8_ZERO: [u8; 2] = [0xC0, 0x80];

/// Takes a byte slice, and attempts to either validate as utf8, or convert to utf8 as appropriate.
///
/// The resultant string should always be smaller than the source cesu8 string (6-byte -> 4-byte, 2-byte nul -> 1-byte)
/// 
/// # Safety
/// This function assumes the interior bytes to be valid Cesu8, depending on the ENCODE_NUL flag.
pub(crate) unsafe fn cesu8_to_utf8<const ENCODE_NUL: bool>(cesu: Cow<[u8]>) -> Cow<str> {
    //  ENCODE_NUL -> cesu8 has no nul, needs re-encoding
    // !ENCODE_NUL -> cesu8 may have nul, leave alone (encoded nul will error)

    debug_assert!(!(ENCODE_NUL && cesu.contains(&b'\0')), "nul-byte included in mutf8 string");

    // try returning it as-is if there are no cesu8/mutf8 specific characters
    let (e, mut cesu) = match std::str::from_utf8(&cesu) {
        Ok(_) => { // valid UTF8 as is
            // SAFETY: previously asserted utf8-ness with std::str::from_utf8
            unsafe {
                return match cesu {
                    Cow::Borrowed(b) => Cow::Borrowed(std::str::from_utf8_unchecked(b)),
                    Cow::Owned(v) => Cow::Owned(String::from_utf8_unchecked(v)),
                };
            }
        },
        Err(e) => { // have to re-encode. all cesu8 should be able to re-encode losslessly as utf8
            // either use the provided, or create a new allocation
            (e, cesu.into_owned())
        }
    };

    // track our current read/write indices. our resultant string will always be smaller:
    // [0xED, _, _, 0xED, _, _] is a 6-byte surrogate pair, which convert into UTF8 4-byte codepoints.
    // [0xC0, 0x80] is a 2-byte encoded nul, which convert into a single nul byte.\

    // [..iw] is valid utf8, whats been written
    // [ir..] is the rest of the cesu8 string, what needs to be read
    // [iw..ir] is scratch space, invalid
    let mut iw = e.valid_up_to(); // written up to
    let mut ir = e.valid_up_to(); // read up to

    while ir < cesu.len() { // continue until we've exhausted our source bytes
        let rest = &mut cesu[ir..];

        // if we're here - found either 6-pair, or (if ENCODE_NUL) a 0xC0,0x80 sequence
        if ENCODE_NUL && rest.starts_with(&MUTF8_ZERO) {
            cesu[iw] = b'0';
            iw += 1; // nul-byte
            ir += 2; // encoded nul-byte
        } else if let Some(slice6) = rest.get_mut(..6) {
            let &mut [first, second, third, fourth, fifth, sixth] = slice6 else { panic!(); };
            debug_assert!(
                first == 0xED && fourth == 0xED,
                "expected surrogate pair, recieved something else (err bytes[..6]: {:x?})",
                &rest[..6]
            );

            let utf8bytes: [u8; 4] = dec_surrogates_infallable(second, third, fifth, sixth);
            slice6[..4].copy_from_slice(&utf8bytes);
            iw += 4;
            ir += 6;
        } else {
            let strtype = if ENCODE_NUL { "MUTF8" } else { "CESU8" };
            let encnulstr = if ENCODE_NUL { "encoded nul or "} else { "" };

            unreachable!(
                "{} decoding error. expected {}surrogate pair, got something else. (string up to this point: {:?}, next few bytes: {:x?})",
                strtype, encnulstr,
                String::from_utf8_lossy(&cesu[..iw]), // lossy just in case - no need to double panic
                &cesu[iw..cesu.len().min(iw+16)],
            );
        }

        // consumed an cesu8/mutf8 character, attempt to continue with utf8
        let valid_utf8 = match std::str::from_utf8(&cesu[ir..]) {
            Ok(s) => s.len(),
            Err(e) => e.valid_up_to(),
        };
        cesu.copy_within(ir..ir+valid_utf8, iw);
        ir += valid_utf8;
        iw += valid_utf8;
        // either consumed the rest of the string, or found a cesu8/mutf8 character
    }

    // should always be true, runtime check helps optimizing the resize call
    debug_assert!(iw < cesu.len());
    if iw < cesu.len() {
        cesu.resize(iw, 0);
    }

    Cow::Owned(match cfg!(debug_assertions) {
        true => String::from_utf8(cesu).expect("reencoded cesu into invalid utf8"),
        // SAFETY: we've reencoded cesu into valid utf8. any re-encoding errors should have been caught by tests
        // or during debug runs.
        false => unsafe { String::from_utf8_unchecked(cesu) }
    })
}

// pub(crate) unsafe fn utf8_to_cesu8<const ENCODE_NUL: bool>(utf: Cow<str>) -> Cow<[u8]> {


//     match crate::encoding::utf8_as_cesu8_spec::<ENCODE_NUL>(text) {

//     }
// }

fn utf8_to_cesu8_piecewise<const ENCODE_NUL: bool>(b: &[u8]) -> Option<usize> {
    pub fn invalid_byte<const ENCODE_NUL: bool>(b: u8) -> bool {
        (ENCODE_NUL && b == 0) || (b & TAG_LEN4_MASK) == TAG_LEN4_VAL
    }
    b.iter().copied().position(invalid_byte::<ENCODE_NUL>)
}

fn utf8_to_cesu8_check_lane<const LANES: usize, const ENCODE_NUL: bool>(arr: [u8; LANES]) -> bool
where
    LaneCount<LANES>: SupportedLaneCount
{
    let mask: Simd<u8, LANES> = Simd::splat(TAG_LEN4_MASK); 
    let val: Simd<u8, LANES> = Simd::splat(TAG_LEN4_VAL);
    let zero: Simd<u8, LANES> = Simd::splat(0);

    let chunk = Simd::from_array(arr);
    let utf8_4byte = (chunk & mask).simd_eq(val).any();
    let utf8_nul = ENCODE_NUL && chunk.simd_eq(zero).any();
    utf8_4byte || utf8_nul
}

/// Attempt to use generic SIMD to detect invalid CESU-8 (4-byte UTF-8 codepoints)/MUTF-8 (CESU-8 + nul-bytes) sequences within a UTF-8 string
///
/// There are a few generic parameters do adjust the functionality or optimization of this function:
/// `CHUNK_SIZE`: determines the number of elements to attempt to process at once
/// The other two parameters determine if this function uses SIMD for the last `b.len() % CHUNK_SIZE` bytes.
/// * `MIN_SIMD`: Do not use SIMD if `remaining_bytes.len() < MIN_SIND`. init penalty of simd is too high
/// * `MIN_SIMD_FACTOR`: Do not use SIMD if `remaining_bytes.len() < CHUNK_SIZE/MIN_SIMD_FACTOR`. for larger chunk sizes, eg: use chunks of 64 but still SIMD process those > 16 bytes
pub(crate) fn utf8_to_cesu8_simd<const CHUNK_SIZE: usize, const MIN_SIMD: usize, const MIN_SIMD_FACTOR: usize, const ENCODE_NUL: bool>(b: &[u8]) -> Option<usize>
where
    LaneCount<CHUNK_SIZE>: SupportedLaneCount
{
    let (chunk_start, chunk) = (0..b.len()).step_by(CHUNK_SIZE)
        .filter_map(|i| {
            let chunk = b.get(i..i+CHUNK_SIZE)?; // only full chunks of N
            let chunkarr = chunk.try_into().unwrap();
            utf8_to_cesu8_check_lane::<CHUNK_SIZE, ENCODE_NUL>(chunkarr).then_some((i, chunk))
        })
        .next() // Some(_) iff there is already an invalid chunk
        .or_else(|| { // found none, previously checked all chunks of CHUNK_SIZE, check end?
            let r = b.len() % CHUNK_SIZE;
            if r == 0 { return None; } // no partial chunks to check
            
            let i = b.len()-r;
            let rest = &b[i..];

            if r < MIN_SIMD || r < CHUNK_SIZE/MIN_SIMD_FACTOR {
                return Some((i, rest)); // don't bother trying simd
            }

            let mut arr = [b'#'; CHUNK_SIZE];
            arr[..r].copy_from_slice(&rest);
            utf8_to_cesu8_check_lane::<CHUNK_SIZE, ENCODE_NUL>(arr).then_some((i, rest))
            // return Some(_) if the chunk is invalid, otherwise None
        })?;
    
    // found either:
    // bad chunk, whole or partial
    // chunk to manually check, chunk < MIN_SIMD || chunk < CHUNK_SIZE/MIN_SIMD_FACTOR
    utf8_to_cesu8_piecewise::<ENCODE_NUL>(chunk).map(|i| chunk_start+i)
}

/// Checks a utf8 string (as bytes) for validity. Returns the position of the error. That is, `b[..returned_index]` is valid.
/// 
/// If this function returns None, there was no error.
pub(crate) fn check_utf8_to_cesu8<const CHUNK_SIZE: usize, const ENCODE_NUL: bool>(b: &[u8]) -> Option<usize> {
    // TODO: map output to Result<&[u8], usize>
    utf8_to_cesu8_simd::<DEFAULT_CHUNK, {DEFAULT_CHUNK/2}, 2, ENCODE_NUL>(b)
}

/// Convert a known-UTF8 string into CESU8 string
/// 
/// The bytes provided should never contain a nul terminator.
/// 
/// The `ADD_NUL` flag is provided as a convience to add a nul byte to the end of allocated outputs.
pub(crate) fn utf8_to_cesu8_vec<const CHUNK_SIZE: usize, const ENCODE_NUL: bool>(src: Cow<str>) -> Cow<[u8]> {    
    let Some(first_bad_idx) = check_utf8_to_cesu8::<CHUNK_SIZE, true>(src.as_bytes()) else {
        // SAFETY: utf8_to_cesu8 would have returned Some(_) on cesu8 error
        return match src {
            Cow::Borrowed(s) => Cow::Borrowed(s.as_bytes()),
            Cow::Owned(s) => Cow::Owned(s.into_bytes()),
        };
    };

    let mut dst = Vec::with_capacity(crate::default_cesu8_capacity(src.len()));
    let (valid, rest) = src.split_at(first_bad_idx);
    dst.extend_from_slice(valid.as_bytes()); // initial push
    utf8_to_cesu8_io::<CHUNK_SIZE, ENCODE_NUL, _>(rest, true, &mut dst).unwrap(); // Vec's io::Write cannot error
    Cow::Owned(dst)
}

/// Converts a UTF-8 string directly through the std::io::Write trait.
#[inline]
pub(crate) fn utf8_to_cesu8_io<const CHUNK_SIZE: usize, const ENCODE_NUL: bool, W: io::Write>(mut src: &str, hint_bad_start: bool, mut w: W) -> io::Result<()> {
    loop {
        let artificial_err = (src.len() > 0 && hint_bad_start).then_some(0);
        let err_ind_opt = artificial_err.or_else(|| check_utf8_to_cesu8::<CHUNK_SIZE, true>(src.as_bytes()));
        match err_ind_opt {
            None if src.len() == 0 => { return Ok(()); }
            None => { // rest is good
                return w.write_all(src.as_bytes());
            },
            Some(err_ind) => { // found cesu8 (possible) error at err_ind
                
                // write the valid portion, and mark it consumed
                let (valid, rest) = src.split_at(err_ind);
                if valid.len() > 0 {
                    w.write_all(valid.as_bytes())?;
                }
                src = rest;

                // extract the next char, which could be invalid cesu8 and definitely exists
                let mut chars = src.chars();
                let Some(ch) = chars.next() else {
                    // should never actually trigger
                    // a zero-length string should be valid
                    // err_ind should never be at the end (since it would be entirely valid)
                    unreachable!();
                };
                
                if ENCODE_NUL && ch == '\0' {
                    // reencode nul as 2-byte pair
                    w.write_all(MUTF8_ZERO.as_slice())?;
                    src = chars.as_str(); // "consume" the character
                } else if ch.len_utf8() == 4 {
                    // reencode 4-byte sequence as 2 3-byte sequences
                    let cesu_bytes = enc_surrogates(ch as u32);
                    w.write_all(&cesu_bytes)?;
                    src = chars.as_str(); // "consume" the character
                }

                // explicitly do not update src string/consume char if the character was valid
                // so check_utf8_to_cesu8 can operate on hint_bad_start
            }
        }
    }
}

pub fn utf8_to_cesu8_string<const CHUNK_SIZE: usize, const ENCODE_NUL: bool>(src: Cow<str>) -> Cow<[u8]> {
    let Some(first_bad_idx) = check_utf8_to_cesu8::<CHUNK_SIZE, true>(src.as_bytes()) else {
        // SAFETY: utf8_to_cesu8 would have returned Some(_) on cesu8 error
        return match src {
            Cow::Borrowed(s) => Cow::Borrowed(s.as_bytes()),
            Cow::Owned(s) => Cow::Owned(s.into_bytes()),
        }
    };

    let mut dst = Vec::with_capacity(crate::default_cesu8_capacity(src.len()));
    dst.extend_from_slice(&src.as_bytes()[..first_bad_idx]); // initial push
    let mut src = &src[first_bad_idx..];
    
    loop {
        let mut chars = src.chars();
        let Some(ch) = chars.next() else {
            // nothing left to convert
            break;
        };
        src = chars.as_str();

        if ENCODE_NUL && ch == '\0' {
            dst.push(b'\0');
        } else {
            debug_assert_eq!(ch.len_utf8(), 4, "signaled to encode utf8 sequence that isn't nul byte or of length four");
            let cesu_bytes = enc_surrogates(ch as u32);
            dst.extend_from_slice(&cesu_bytes);
        };

        let use_next_utf8 = check_utf8_to_cesu8::<CHUNK_SIZE, true>(&src.as_bytes())
            .unwrap_or(src.len());

        let (consumed, rest) = src.split_at(use_next_utf8);
        dst.extend_from_slice(consumed.as_bytes());
        src = rest;
    }

    // we've converted everything, and had to allocate
    Cow::Owned(dst)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct EncodingError {
    pub(crate) valid_up_to: usize,
    pub(crate) error_len: Option<NonZeroU8>,
}

impl EncodingError {
    pub fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }
    pub fn error_len(&self) -> Option<NonZeroU8> {
        self.error_len
    }
}

/// Matches exactly one CESU8/MUTF8 sequence, erroring if any other value (or not enough bytes) is found.
/// * `Ok(length)` if a character was found
/// * `Err(Some(()))` if an error was found
/// * `Err(None)` if more information is needed
#[inline(never)]
fn valid_cesu8_char<const ENCODE_NUL: bool>(b: &[u8]) -> Result<usize, Option<()>> {
    let not_enough = Err(None);
    match &b {
        [0xC0] if ENCODE_NUL => not_enough,
        [0xC0, 0x80, ..] if ENCODE_NUL => {
            // found encoded nul
            Ok(2)
        },
        [0xED] => not_enough,
        [0xED, _] => not_enough,
        [0xED, _, _] => not_enough,
        [0xED, _, _, 0xED] => not_enough,
        [0xED, _, _, 0xED, _] => not_enough,
        [0xED, b2, b3, 0xED, b5, b6, ..] => {
            // found surrogate pair
            dec_surrogates::<true>(*b2, *b3, *b5, *b6)
                .map(|_| 6)
                .map_err(|_| Some(()))
        }
        _ => { Err(Some(())) }
    }
}

pub(crate) fn validate_cesu8<const CHUNK_SIZE: usize, const ENCODE_NUL: bool>(source: &[u8]) -> Result<(), EncodingError> {
    // TODO: rework this function to not use unsafeaw
    
    use std::slice::SliceIndex;
    fn subslice<I: SliceIndex<[u8]>>(buf: &[u8], r: I) -> &<I as SliceIndex<[u8]>>::Output {
        if cfg!(debug_assertions) {
            &buf[r]
        } else {
            unsafe { buf.get_unchecked(r) }
        }
    }
    let mut base = 0;
    loop {
        let (valid_utf8, utf8_err) = match std::str::from_utf8(subslice(source, base..)) {
            Ok(s) => (s.as_bytes(), Ok(())),
            Err(e) => (
                subslice(source, base..base+e.valid_up_to()),
                Err(e.error_len())
            ),
        };
        let cesu8_err = check_utf8_to_cesu8::<CHUNK_SIZE, ENCODE_NUL>(valid_utf8);
        match (cesu8_err, utf8_err) {
            // bad cesu8 in valid utf8
            (Some(i), _) => return Err(EncodingError {
                valid_up_to: base + i,
                error_len: Some(1.try_into().unwrap()),
            }),

            // both valid utf8/cesu8
            (None, Ok(())) => return Ok(()),

            // valid cesu8, not enough utf8 afterwards
            (None, Err(None)) => return Err(EncodingError {
                valid_up_to: base + valid_utf8.len(),
                error_len: None,
            }),

            // valid cesu8, invalid utf8 sequence, might be valid cesu8?
            (None, Err(Some(bad_utf8_len))) => {
                base += valid_utf8.len();

                // check for cesu8/mutf8 sequences, returning a 'not enough bytes' error if more could lead to a valid sequence
                match valid_cesu8_char::<true>(subslice(source, base..)) {
                    // valid cesu8 sequence, 'consume' that part
                    Ok(len) => {
                        base += len;
                    },

                    // may be able to complete sequence with more info
                    Err(None) => return Err(EncodingError {
                        valid_up_to: base,
                        error_len: None,
                    }),

                    // found no recognized sequence - passthrough utf8 error
                    Err(Some(())) => return Err(EncodingError {
                        valid_up_to: base,
                        error_len: Some((bad_utf8_len as u8).try_into().unwrap()),
                    }),
                }
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct InvalidCesu8SurrogatePair([u8; 4]);
impl Error for InvalidCesu8SurrogatePair {}
impl fmt::Display for InvalidCesu8SurrogatePair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f,
            "attempt to decode invalid cesu-8 6-byte surrogate pair: {:x?}",
            &[0xED, self.0[0], self.0[1], 0xED, self.0[2], self.0[3]]
        )
    }
}

#[inline]
pub(crate) fn dec_surrogates_infallable(second: u8, third: u8, fifth: u8, sixth: u8) -> [u8; 4] {
    if cfg!(debug_assertions) {
        dec_surrogates::<true>(second, third, fifth, sixth).expect("failed cesu surrogate pair decode when expected to be infallible")
    } else {
        // checks runtime are compiled out in this branch
        dec_surrogates::<false>(second, third, fifth, sixth).unwrap()
    }
}

/// Convert the bytes from a CESU-8 surrogate pair into a valid UTF-8
/// sequence. If not `CHECK_INVALID`, then input is not validated.
#[inline]
pub(crate) fn dec_surrogates<const CHECK_INVALID: bool>(second: u8, third: u8, fifth: u8, sixth: u8) -> Result<[u8; 4], InvalidCesu8SurrogatePair> {
    /// Convert the two trailing bytes from a CESU-8 surrogate to a regular
    /// surrogate value.
    fn dec_surrogate(second: u8, third: u8) -> u32 {
        0xD000u32 | ((second & CONT_MASK) as u32) << 6 | (third & CONT_MASK) as u32
    }
    
    if CHECK_INVALID {
        //- from_utf8 should consume any valid three-bytes sequences
        // if our three-byte surrogate pairs are invalid, they'll be caught here

        // assert our continuation bytes are indeed continuations
        // assert our second & fifth bytes are on the right side of each other
        let invalid_pair = Err(InvalidCesu8SurrogatePair([second, third, fifth, sixth]));
        if (second & !CONT_MASK) != TAG_CONT_U8 { return invalid_pair; }
        if (second & 0b1111_0000) != 0b1010_0000 { return invalid_pair; }
        if (third & !CONT_MASK) != TAG_CONT_U8 { return invalid_pair; }
        if (fifth & !CONT_MASK) != TAG_CONT_U8 { return invalid_pair; }
        if (fifth & 0b1111_0000) != 0b1011_0000 { return invalid_pair; }
        if (sixth & !CONT_MASK) != TAG_CONT_U8 { return invalid_pair; }
    }
    
    // Convert to a 32-bit code point.
    let s1 = dec_surrogate(second, third);
    let s2 = dec_surrogate(fifth, sixth);
    let c = 0x10000 + (((s1 - 0xD800) << 10) | (s2 - 0xDC00));

    //println!("{:0>8b} {:0>8b} {:0>8b} -> {:0>16b}", 0xEDu8, second, third, s1);
    //println!("{:0>8b} {:0>8b} {:0>8b} -> {:0>16b}", 0xEDu8, fifth, sixth, s2);
    //println!("-> {:0>32b}", c);

    if CHECK_INVALID && !(0x010000..=0x10FFFF).contains(&c) {
        return Err(InvalidCesu8SurrogatePair([second, third, fifth, sixth]));
    }

    // Convert to UTF-8.
    // 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    Ok([
        0b1111_0000u8 | ((c & 0b1_1100_0000_0000_0000_0000) >> 18) as u8,
        TAG_CONT_U8   | ((c & 0b0_0011_1111_0000_0000_0000) >> 12) as u8,
        TAG_CONT_U8   | ((c & 0b0_0000_0000_1111_1100_0000) >> 6) as u8,
        TAG_CONT_U8   | ( c & 0b0_0000_0000_0000_0011_1111) as u8,
    ])
}


#[inline]
pub(crate) fn enc_surrogates(ch: u32) -> [u8; 6] {
    // encode `ch` into a supplementary UTF-16 pair (`high` and `low`), then convert the raw pair data to (invalid) UTF-8

    /// Encode a single surrogate as CESU-8.
    #[inline]
    fn enc_surrogate(surrogate: u16) -> [u8; 3] {
        if cfg!(debug_assertions) || cfg!(validate_release) {
            assert!(
                (0xD800..=0xDFFF).contains(&surrogate),
                "trying to encode invalid surrogate pair"
            );
        }
        // 1110xxxx 10xxxxxx 10xxxxxx
        [
            0b11100000 | ((surrogate & 0b1111_0000_0000_0000) >> 12) as u8,
            TAG_CONT_U8 | ((surrogate & 0b0000_1111_1100_0000) >> 6) as u8,
            TAG_CONT_U8 | (surrogate & 0b0000_0000_0011_1111) as u8,
        ]
    }

    let c = ch - 0x10000;
    let high = enc_surrogate(((c >> 10) as u16) | 0xD800);
    let low = enc_surrogate(((c & 0x3FF) as u16) | 0xDC00);

    [high[0], high[1], high[2], low[0], low[1], low[2]]
}


