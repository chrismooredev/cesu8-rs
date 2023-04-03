use std::borrow::Cow;
use std::str::Utf8Error;

use crate::encoding::utf8err_new;
use crate::ngstr::prims::{enc_surrogates, dec_surrogates};
use crate::preamble::*;

// not a proper character? but it validates through std::char::from_u32(0xd7ff) and it kinda stands out visually
// notably: it starts with ED: \xED\x90\x90
const THREE_BYTE_ED_CHAR: char = '\u{d410}';
const THREE_BYTE_ED_UTF8: &'static str = "\u{d410}";

const PURPLE_CIRCLE_UTF8: &'static str = "\u{1f7e3}";
const PURPLE_CIRCLE_CHAR: char = '🟣';
const PURPLE_CIRCLE_CESU8: &'static [u8] = b"\xED\xA0\xBD\xED\xBF\xA3";

// const PURPLE_HEART_CHAR: char = '💜';
// const PURPLE_HEART_UTF8: &'static str = "\u{1f49c}";
// const PURPLE_HEART_CESU8: &'static [u8] = "";

mod chars {
    use super::*;

    #[test]
    fn utf8_references() {
        assert_eq!(THREE_BYTE_ED_UTF8.chars().next().unwrap(), THREE_BYTE_ED_CHAR);

        assert_eq!(PURPLE_CIRCLE_UTF8.chars().next().unwrap(), PURPLE_CIRCLE_CHAR);
        let bytes = enc_surrogates(PURPLE_CIRCLE_CHAR as u32);
        assert_eq!(bytes, PURPLE_CIRCLE_CESU8);
    }
}

mod string {
    use std::assert_matches::assert_matches;

    use super::*;

    macro_rules! test_encoded {
        ($($STR:ty),+, $text:literal, $expected:literal) => {
            $({
                eprintln!("[{}][{:?}] converting from utf8...", std::any::type_name::<$STR>(), $text);
                let cesu8 = <$STR>::from_utf8($text);

                assert_eq!(
                    $expected, cesu8.as_bytes(),
                    "[{}][{:?}] unable to properly encode to CESU-8",
                    std::any::type_name::<$STR>(), $text
                );

                eprintln!("[{}][{:?}] converting back to utf8... (prev cesu bytes: {:X?})", std::any::type_name::<$STR>(), $text, cesu8._raw_bytes());
                let utf8 = cesu8.to_str();
                assert_eq!(
                    $text, utf8,
                    "[{}][{:?}] bad roundtrip from UTF-8 to CESU-8 to UTF-8",
                    std::any::type_name::<$STR>(), $text
                );
            })+
        };
        // ($($S:ty),+, $text:literal, $expected:literal) => {
        //     text_encoded_!($S, $text, $expected);
        //     text_encoded_!($($S),+, $text, $expected);
        // };
    }

    // fn test_encoded_same(text: &str, expected: &[u8]) {
    //     test_encoded::<Cesu8String>(text, expected);
    //     test_encoded::<Mutf8String>(text, expected);
    // }

    fn test_surrogates(ch: char, expected: &[u8; 6]) {
        let encoded = enc_surrogates(ch as u32);
        assert_eq!(
            expected, &encoded,
            "enc_surrogates returned unexpected encoded character"
        );

        let decoded = dec_surrogates::<true>(encoded[1], encoded[2], encoded[4], encoded[5]).unwrap();
        let decoded_ch = std::str::from_utf8(&decoded)
            .expect("dec_surrogates returned invalid UTF-8")
            .chars()
            .next()
            .unwrap();

        assert_eq!(
            ch, decoded_ch,
            "dec_surrogates returned unexpected character"
        );
    }

    #[test]
    fn surrogates() {
        test_surrogates('🟣', b"\xED\xA0\xBD\xED\xBF\xA3");
    }

    #[test]
    fn embedded_nuls() {
        test_encoded!(Cesu8Str, "plain", b"plain");
        test_encoded!(Cesu8Str, "start\0end", b"start\0end");
        test_encoded!(Cesu8Str, "\0middle\0", b"\0middle\0");
        test_encoded!(Cesu8Str, "\0\0\0", b"\0\0\0");

        test_encoded!(Mutf8Str, "plain", b"plain");
        test_encoded!(Mutf8Str, "start\0end", b"start\xC0\x80end");
        test_encoded!(Mutf8Str, "\0middle\0", b"\xC0\x80middle\xC0\x80");
        test_encoded!(Mutf8Str, "\0\0\0", b"\xC0\x80\xC0\x80\xC0\x80");
    }

    #[test]
    fn supplementary_pairs() {
        // TODO: refactor these to use concat_bytes! if/when implemented/stablized
        // TODO: Use a variety of different characters? (though all 4-byte chars should be handled exactly the same)
        assert_eq!("🟣".len(), 4);
        assert_eq!("🟣".as_bytes(), b"\xf0\x9f\x9f\xa3");
        assert_eq!(&enc_surrogates('🟣' as u32), b"\xED\xA0\xBD\xED\xBF\xA3");

        // These should encode as the same, whether its java variant or not
        test_encoded!(Cesu8Str, Mutf8Str, "plain", b"plain");
        test_encoded!(Cesu8Str, Mutf8Str, "start🟣end", b"start\xED\xA0\xBD\xED\xBF\xA3end");
        test_encoded!(Cesu8Str, Mutf8Str,
            "🟣middle🟣",
            b"\xED\xA0\xBD\xED\xBF\xA3middle\xED\xA0\xBD\xED\xBF\xA3"
        );
        test_encoded!(Cesu8Str, Mutf8Str,
            "🟣🟣🟣",
            b"\xED\xA0\xBD\xED\xBF\xA3\xED\xA0\xBD\xED\xBF\xA3\xED\xA0\xBD\xED\xBF\xA3"
        );
    }

    #[test]
    fn cesu8_from_utf8_into_buf_nocopy() {
        // no reencoding necessary - use the original string, skipping the buffer
        let text = "hello\0";
        let mut buf = [0; 0];
        let cows = Cesu8Str::from_utf8_into_buf(text, &mut buf);
        assert_matches!(cows, Cow::Borrowed(_), "didn't reuse original string when re-encoding unnecessary");
        assert_eq!(cows.as_bytes(), text.as_bytes());
    }

    #[test]
    fn mutf8_from_utf8_into_buf_with_space() {
        // reencode into a perfectly sized buffer
        let text = "hello\0";
        let mut buf = [0; 7];
        let cows = Mutf8Str::from_utf8_into_buf(text, &mut buf);
        assert_matches!(cows, Cow::Borrowed(_), "didn't use provided stack buf when re-encoding with enough space");
        assert_eq!(b"hello\xC0\x80", cows.as_bytes(), "bad reencoding");
    }

    #[test]
    fn mutf8c_from_utf8_into_buf_with_space() {
        // reencode into a perfectly sized buffer
        let text = "hello\0";
        let mut buf = [0; 8];
        let cows = Mutf8CStr::from_utf8_into_buf(text, &mut buf);
        assert_matches!(cows, Cow::Borrowed(_), "didn't use provided stack buf when re-encoding with enough space");
        assert_eq!(b"hello\xC0\x80\0", cows.as_bytes_with_nul(), "bad reencoding");
    }
    
    #[test]
    fn mutf8_from_utf8_into_buf_without_space() {
        // try to reencode into too small buffer - error (no space for reencoding nul)
        // assert error state is as expected
        let text = "hello\0";
        let mut buf = [0; 6]; // uhoh - forgot space to reencode nul!
        let res = Mutf8Str::try_from_utf8_into_buf(text, &mut buf);
        let Err(err) = res else {
            panic!("didn't error on too-small buffer when reallocation not requested");
        };
        assert_eq!(b"hello", err.encoded_bytes(), "not enough space, partial codepoints were written?");
        assert_eq!(5, err.bytes_read(), "unexpected number of bytes consumed");
        assert_eq!("hello", err.source_str_used());
        assert_eq!("\0", err.source_str_rest());
        let allocated: Mutf8String = err.finish();
        assert_eq!(b"hello\xC0\x80", allocated.as_bytes());
    }

    #[test]
    fn mutf8c_from_utf8_into_buf_without_space_reencode_end() {
        // try to reencode into too small buffer - error (no space for reencoding nul)
        // assert error state is as expected
        let text = "hello\0";
        let mut buf = [0; 6]; // uhoh - forgot space to reencode nul!
        let res = Mutf8CStr::try_from_utf8_into_buf(text, &mut buf);
        let Err(err) = res else {
            panic!("didn't error on too-small buffer when reallocation not requested");
        };
        assert_eq!(b"hello", err.encoded_bytes(), "not enough space, partial codepoints were written?");
        assert_eq!(5, err.bytes_read(), "unexpected number of bytes consumed");
        assert_eq!("hello", err.source_str_used());
        assert_eq!("\0", err.source_str_rest());
        let allocated: Mutf8CString = err.finish();
        assert_eq!(b"hello\xC0\x80\0", allocated.as_bytes_with_nul());
    }
    #[test]
    fn mutf8_from_utf8_into_buf_without_space_reencode_mid() {
        // try to reencode into too small buffer - error (no space for reencoding nul)
        // assert error state is as expected
        let text = "hel\0lo";
        let mut buf = [0; 6]; // uhoh - forgot space to reencode nul!
        let res = Mutf8Str::try_from_utf8_into_buf(text, &mut buf);
        let Err(err) = res else {
            panic!("didn't error on too-small buffer when reallocation not requested");
        };
        assert_eq!(b"hel\xC0\x80l", err.encoded_bytes(), "not enough space, partial codepoints were written?");
        assert_eq!(5, err.bytes_read(), "unexpected number of bytes consumed");
        assert_eq!("hel\0l", err.source_str_used());
        assert_eq!("o", err.source_str_rest());
        let allocated: Mutf8String = err.finish();
        assert_eq!(b"hel\xC0\x80lo", allocated.as_bytes());
    }

    #[test]
    fn mutf8c_from_utf8_into_buf_without_space_for_nul() {
        // try to reencode into too small buffer - error (no space for nul-terminator)
        let text = "hello\0";
        let mut buf = [0; 7]; // uhoh - forgot space to add nul-terminator!
        let res = Mutf8CStr::try_from_utf8_into_buf(text, &mut buf);
        let Err(err) = res else {
            panic!("didn't error on too-small buffer when reallocation not requested");
        };
        assert_eq!(b"hello\xC0\x80", err.encoded_bytes(), "not enough space, partial codepoints were written?");
        assert_eq!(6, err.bytes_read(), "unexpected number of bytes consumed");
        assert_eq!("hello\0", err.source_str_used());
        assert_eq!("", err.source_str_rest());
        let allocated: Mutf8CString = err.finish();
        assert_eq!(b"hello\xC0\x80\0", allocated.as_bytes_with_nul());
    }

    #[test]
    fn mutf8c_from_utf8_into_buf_without_space_for_reencode() {
        // reencode into an owned buffer, provided buffer is too small
        let text = "hello\0";
        let mut buf = [0; 6]; // uhoh - forgot space to reencode nul!
        let cows = Mutf8CStr::from_utf8_into_buf(text, &mut buf);
        assert_matches!(cows, Cow::Owned(_), "didn't reencode to allocated string when buffer to small");
        assert_eq!(b"hello\xC0\x80\0", cows.as_bytes_with_nul(), "bad reencoding");
    }

    #[test]
    fn mutf8c_from_utf8_into_buf_without_space_for_nul_term() {
        // reencode into an owned buffer, provided buffer is too small
        let text = "hello\0";
        let mut buf = [0; 7]; // uhoh - forgot space for a nul terminator!
        let cows = Mutf8CStr::from_utf8_into_buf(text, &mut buf);
        assert_matches!(cows, Cow::Owned(_), "didn't reencode to allocated string when buffer to small");
        assert_eq!(b"hello\xC0\x80\0", cows.as_bytes_with_nul(), "bad reencoding");
    }

    // #[test]
    // fn from_cesu8_lossy() {
    //     use Variant::*;
    //     const _UTF8_REPLACE: &[u8] = b"\xEF\xBF\xBD";

    //     #[track_caller] // keep panic/error lines correct for each subtest
    //     fn assert_lossy<'a, 'b>(
    //         raw: &'a [u8],
    //         lossy: impl AsRef<[u8]>,
    //         variant: Variant,
    //         utf8_err: Result<(), Utf8Error>,
    //     ) {
    //         let parsed = Cesu8Str::from_cesu8_lossy(raw, variant);
    //         assert_eq!(lossy.as_ref(), parsed.as_bytes());
    //         assert_eq!(utf8_err, parsed.utf8_error);
    //     }

    //     assert_lossy(b"my valid string", "my valid string", Standard, Ok(()));

    //     // embedded null char replacement
    //     assert_lossy(b"start\xC0end", "start\u{FFFD}end", Standard, Ok(()));
    //     assert_lossy(b"start\xC0end", "start\u{FFFD}end", Java, Ok(()));

    //     // missing byte on first half surrogate pair
    //     assert_lossy(
    //         b"start\xED\xA0\xED\xBF\xA3end",
    //         "start\u{FFFD}\u{FFFD}end",
    //         Standard,
    //         Ok(()),
    //     );

    //     // missing byte on second surrogate pair
    //     assert_lossy(
    //         b"start\xED\xA0\xBD\xED\xBFend",
    //         "start\u{FFFD}\u{FFFD}end",
    //         Standard,
    //         Ok(()),
    //     );

    //     // missing byte on second surrogate pair, with valid CESU8 for UTF8 error
    //     assert_lossy(
    //         b"start\xED\xA0\xBD\xED\xBF\xA3middle\xED\xA0\xBD\xED\xBFend",
    //         b"start\xED\xA0\xBD\xED\xBF\xA3middle\xEF\xBF\xBD\xEF\xBF\xBDend",
    //         Standard,
    //         Err(utf8err_new(5, Some(1))),
    //     );
    // }
}

mod string_impls {
    use super::*;

    #[test]
    fn eq_across_variants() {
        let reference = "begin\0end";
        let cesu_nul = Cesu8Str::from_utf8(reference);
        let mutf_nul = Mutf8Str::from_utf8(reference);

        // while the bytes should be different, they should still be equilavent
        assert_ne!(cesu_nul.as_bytes(), mutf_nul.as_bytes());
        assert_eq!(cesu_nul, mutf_nul);
    }

    #[test]
    fn add_cesu8() {
        let mut concat = Cesu8Str::from_utf8("begin\0end").into_owned();
        concat = concat + "**basic string🟣";
        concat = concat + Cesu8Str::from_utf8("**owned\0cesu").as_ref();

        assert_eq!(concat.as_bytes(), b"begin\0end**basic string\xED\xA0\xBD\xED\xBF\xA3**owned\0cesu");
    }

    #[test]
    fn add_mutf8c() {
        let mut concat = Mutf8CString::from_utf8_with_nul("begin\0end\0".to_owned());
        concat = concat + "**🟣basic string";
        concat = concat + &*Mutf8CString::from_utf8("**owned\0cesu\0".to_owned());

        assert_eq!(concat.as_bytes_with_nul(), b"begin\xC0\x80end**\xED\xA0\xBD\xED\xBF\xA3basic string**owned\xC0\x80cesu\xC0\x80\0");
    }

}

mod legacy_api {
    use super::*;
    use crate::legacy_api::*;

    #[test]
    fn test_from_cesu8() {
        // The surrogate-encoded character below is from the ICU library's
        // icu/source/test/testdata/conversion.txt test case.
        let data = &[
            0x4D, 0xE6, 0x97, 0xA5, 0xED, 0xA0, 0x81, 0xED, 0xB0, 0x81, 0x7F,
        ];
        assert_eq!(
            Cow::Borrowed("M日\u{10401}\u{7F}"),
            Cesu8Str::try_from_bytes(data).unwrap().to_str()
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

    
    #[test]
    fn test_valid_cesu8() {
        assert!(is_valid_cesu8("aé日"));
        assert!(is_valid_java_cesu8("aé日"));
        assert!(!is_valid_cesu8("\u{10401}"));
        assert!(!is_valid_java_cesu8("\u{10401}"));
        assert!(is_valid_cesu8("\0\0"));
        assert!(!is_valid_java_cesu8("\0\0"));
    }
}

mod decoding {
    use crate::Cesu8Error;
    use crate::decoding::until_next_codepoint;

    use super::*;

    #[test]
    fn next_codepoint() {
        assert_eq!(
            1,
            until_next_codepoint(b"++\xC0\x80++", 0, Ok(()))
                .error_len()
                .unwrap()
        );
        assert_eq!(
            2,
            until_next_codepoint(b"++\xC0\x80++", 2, Ok(()))
                .error_len()
                .unwrap()
        );
        assert_eq!(
            1,
            until_next_codepoint(b"++\xC0\x80++", 4, Ok(()))
                .error_len()
                .unwrap()
        );
    }
    #[test]
    #[should_panic]
    fn next_codepoint_past_slice_length() {
        // should panic as it should skip 'past' the end of the string
        until_next_codepoint(b"++\xC0\x80++", 6, Ok(()));
    }

    #[test]
    fn next_codepoint_embedded_nul() {
        const BYTES: &[u8] = b"A \xC0\x80 ";
        let dummy_utf8_err = utf8err_new(2, Some(1));
        let err_with_skip = until_next_codepoint(BYTES, 2, Err(dummy_utf8_err));
        assert_eq!(
            Cesu8Error::new(2, Some(2), Err(dummy_utf8_err)),
            err_with_skip
        );
    }

    #[test]
    fn cesu8_sequences_are_invalid_utf8() {
        use crate::encoding::utf8err_new;
        // These should always be held correct, as it is what makes CESU-8 different to UTF-8

        // b"CESU8" // "UTF8"
        const WITH_SURROGATE: &[u8] = b"surrogate\xED\xA0\xBD\xED\xBF\xA3pair"; // "surrogate🟣pair"
        const WITH_NUL: &[u8] = b"my\xC0\x80string"; // "my\0string"

        assert_eq!(
            std::str::from_utf8(WITH_SURROGATE),
            Err(utf8err_new(9, Some(1)))
        );
        assert_eq!(std::str::from_utf8(WITH_NUL), Err(utf8err_new(2, Some(1))));
    }

    #[test]
    fn utf8_error_len_is_propagated() {
        // we have valid CESU-8, followed by invalid (cut-short) UTF-8
        // 0xE6 starts a 3-byte UTF-8 sequence that is cut short
        const TEST_DATA: &[u8] = b"\xED\xA4\xB8\xED\xB1\xA0\xE6\x82"; 

        let err = Cesu8Str::try_from_bytes(TEST_DATA)
            .expect_err("unterminated 3-byte UTF-8 sequence should cause CESU-8 error");

        // proper CESU-8 error should report we need more data to finish the sequence
        assert_eq!(
            None,
            err.error_len(),
            "should need more data to finish 3-byte UTF-8 sequence"
        );
        assert_eq!(
            6,
            err.valid_up_to(),
            "CESU-8 error should be valid until unterminated UTF-8"
        );

        // test proper string internal assertions are still held
        let valid = Cesu8Str::try_from_bytes(&TEST_DATA[..err.valid_up_to()])
            .expect("removing invalid portion should result in valid CESU-8");
        assert_eq!(valid.as_bytes(), b"\xED\xA4\xB8\xED\xB1\xA0");
    }

    #[test]
    fn utf8_error_len_is_propagated_separated() {
        // we have valid CESU-8, followed by invalid (cut-short) UTF-8
        // 0xE6 starts a 3-byte UTF-8 sequence that is cut short
        // added space to exercise different code paths
        const TEST_DATA: &[u8] = b"\xED\xA4\xB8\xED\xB1\xA0 \xE6\x82";

        let err = Cesu8Str::try_from_bytes(TEST_DATA)
            .expect_err("unterminated 3-byte UTF-8 sequence should cause CESU-8 error");

        // proper CESU-8 error should report we need more data to finish the sequence
        assert_eq!(
            None,
            err.error_len(),
            "should need more data to finish 3-byte UTF-8 sequence"
        );
        assert_eq!(
            7,
            err.valid_up_to(),
            "CESU-8 error should be valid until unterminated UTF-8"
        );

        // test proper string internal assertions are still held
        let valid = Cesu8Str::try_from_bytes(&TEST_DATA[..err.valid_up_to()])
            .expect("removing invalid portion should result in valid CESU-8");
        assert_eq!(valid.as_bytes(), b"\xED\xA4\xB8\xED\xB1\xA0 ");
    }

    #[test]
    fn non_cesu_ed() {
        // test that valid 3-byte UTF-8 sequences starting with '0xED' are still recognized as valid UTF-8,
        // even when between CESU-8 sequences starting with 0xED

        // let bytes = b"\xed\x8d\xad";
        // last three bytes are valid UTF-8, first 6 are CESU-8 surrogate pair
        let bytes = b"\xED\xA0\xBD\xED\xBF\xA3\xED\x90\x90";
        // let as_str = std::str::from_utf8(bytes).unwrap();

        let valid = Cesu8Str::try_from_bytes(bytes).unwrap();
        assert_eq!(valid.to_str(), "🟣\u{d410}")
    }
}
