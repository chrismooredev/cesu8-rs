use std::borrow::Cow;
use std::str::Utf8Error;

use crate::encoding::utf8err_new;
use crate::ngstr::prims::{enc_surrogates, dec_surrogates};
use crate::{Variant, Cesu8Str};

mod string {
    use super::*;

    fn test_encoded(variant: Variant, text: &str, expected: &[u8]) {
        // eprintln!("testing {:?} for variant {:?} as cesu8 from utf8", text, variant);


        let cesu8 = Cesu8Str::from_utf8(text, variant);
        assert_eq!(
            expected,
            cesu8.as_bytes(),
            "[{:?} variant][{:?}] unable to properly encode to CESU-8",
            variant,
            text
        );

        // eprintln!("\tgetting utf8 error for expected");
        let utf8_err = std::str::from_utf8(expected).map(|_| ());
        assert_eq!(
            utf8_err,
            cesu8.utf8_error,
            "[{:?} variant][{:?}] utf8_err invariant was not maintained (CESU-8 bytes: {:x?})",
            variant,
            text,
            cesu8.as_bytes()
        );

        // eprintln!("\treencoding {:?} from cesu8 ({:?}) to utf8", text, expected);
        let utf8 = cesu8.to_str();
        assert_eq!(
            text, utf8,
            "[{:?} variant][{:?}] unexpected decoding from CESU-8 to UTF-8",
            variant, text
        )
    }
    fn test_encoded_same(text: &str, expected: &[u8]) {
        test_encoded(Variant::Standard, text, expected);
        test_encoded(Variant::Java, text, expected);
    }

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
        test_encoded(Variant::Standard, "plain", b"plain");
        test_encoded(Variant::Standard, "start\0end", b"start\0end");
        test_encoded(Variant::Standard, "\0middle\0", b"\0middle\0");
        test_encoded(Variant::Standard, "\0\0\0", b"\0\0\0");

        test_encoded(Variant::Java, "plain", b"plain");
        test_encoded(Variant::Java, "start\0end", b"start\xC0\x80end");
        test_encoded(Variant::Java, "\0middle\0", b"\xC0\x80middle\xC0\x80");
        test_encoded(Variant::Java, "\0\0\0", b"\xC0\x80\xC0\x80\xC0\x80");
    }

    #[test]
    fn supplementary_pairs() {
        // TODO: refactor these to use concat_bytes! if/when implemented/stablized
        // TODO: Use a variety of different characters? (though all 4-byte chars should be handled exactly the same)
        assert_eq!("🟣".len(), 4);
        assert_eq!("🟣".as_bytes(), b"\xf0\x9f\x9f\xa3");
        assert_eq!(&enc_surrogates('🟣' as u32), b"\xED\xA0\xBD\xED\xBF\xA3");

        // These should encode as the same, whether its java variant or not
        test_encoded_same("plain", b"plain");
        test_encoded_same("start🟣end", b"start\xED\xA0\xBD\xED\xBF\xA3end");
        test_encoded_same(
            "🟣middle🟣",
            b"\xED\xA0\xBD\xED\xBF\xA3middle\xED\xA0\xBD\xED\xBF\xA3",
        );
        test_encoded_same(
            "🟣🟣🟣",
            b"\xED\xA0\xBD\xED\xBF\xA3\xED\xA0\xBD\xED\xBF\xA3\xED\xA0\xBD\xED\xBF\xA3",
        );
    }

    #[test]
    fn from_utf8_inplace() {
        let text = "hello\0";

        // reuse string
        {
            // buffer shouldn't even be used - leave it at length 0
            let mut buf = [0; 0];
            let std = Cesu8Str::from_utf8_inplace(text, &mut buf, Variant::Standard)
                .expect("string to be literal, no io necessary");

            // if borrowed, it comes from the `text` as `buf` is zero-length
            assert!(
                matches!(std.bytes, Cow::Borrowed(_)),
                "did not use str data for Cesu8Str"
            );
        }

        // use buffer
        {
            // buffer shouldn't even be used - leave it at length 0
            let mut buf = [0; 16];
            let std = Cesu8Str::from_utf8_inplace(text, &mut buf, Variant::Java)
                .expect("there was not enough space in buf");

            // if borrowed, it comes from the `buf` as `text` would have to change
            assert!(
                matches!(std.bytes, Cow::Borrowed(_)),
                "did not use str data for Cesu8Str"
            );
            assert_eq!(std.bytes.len(), 7, "string length was not as expected");
        }

        // not enough space
        {
            // buffer shouldn't even be used - leave it at length 0
            let mut buf = [0; 0];
            // needs to be Java variant to prevent borrowing from `text`
            let res = Cesu8Str::from_utf8_inplace(text, &mut buf, Variant::Java);

            assert!(
                res.is_err(),
                "there was enough space in buf, with 0-length buf (res = {:?})",
                res
            );
        }
    }

    #[test]
    fn from_cesu8_lossy() {
        use Variant::*;
        const _UTF8_REPLACE: &[u8] = b"\xEF\xBF\xBD";

        #[track_caller] // keep panic/error lines correct for each subtest
        fn assert_lossy<'a, 'b>(
            raw: &'a [u8],
            lossy: impl AsRef<[u8]>,
            variant: Variant,
            utf8_err: Result<(), Utf8Error>,
        ) {
            let parsed = Cesu8Str::from_cesu8_lossy(raw, variant);
            assert_eq!(lossy.as_ref(), parsed.as_bytes());
            assert_eq!(utf8_err, parsed.utf8_error);
        }

        assert_lossy(b"my valid string", "my valid string", Standard, Ok(()));

        // embedded null char replacement
        assert_lossy(b"start\xC0end", "start\u{FFFD}end", Standard, Ok(()));
        assert_lossy(b"start\xC0end", "start\u{FFFD}end", Java, Ok(()));

        // missing byte on first half surrogate pair
        assert_lossy(
            b"start\xED\xA0\xED\xBF\xA3end",
            "start\u{FFFD}\u{FFFD}end",
            Standard,
            Ok(()),
        );

        // missing byte on second surrogate pair
        assert_lossy(
            b"start\xED\xA0\xBD\xED\xBFend",
            "start\u{FFFD}\u{FFFD}end",
            Standard,
            Ok(()),
        );

        // missing byte on second surrogate pair, with valid CESU8 for UTF8 error
        assert_lossy(
            b"start\xED\xA0\xBD\xED\xBF\xA3middle\xED\xA0\xBD\xED\xBFend",
            b"start\xED\xA0\xBD\xED\xBF\xA3middle\xEF\xBF\xBD\xEF\xBF\xBDend",
            Standard,
            Err(utf8err_new(5, Some(1))),
        );
    }
}

mod string_impls {
    use super::*;

    #[test]
    fn eq_across_variants() {
        let reference = "begin\0end";
        let cesu_nul = Cesu8Str::from_utf8(reference, Variant::Standard);
        let mutf_nul = Cesu8Str::from_utf8(reference, Variant::Java);

        // while the bytes should be different, they should still be equilavent
        assert_ne!(cesu_nul.as_bytes(), mutf_nul.as_bytes());
        assert_eq!(cesu_nul, mutf_nul);
    }

    #[test]
    fn add_strings() {
        let mut concat = Cesu8Str::from_utf8("begin\0end", Variant::Standard);
        concat = concat + "**basic string";
        concat = concat + &Cesu8Str::from_utf8("**owned\0cesu", Variant::Java);

        assert_eq!(concat.as_bytes(), b"begin\0end**basic string**owned\0cesu");

        let mut addassign = Cesu8Str::from_utf8("begin\0end", Variant::Standard);
        addassign += "**basic string";
        addassign += &Cesu8Str::from_utf8("**owned\0cesu", Variant::Java); // add a Java variant to a standard string

        assert_eq!(
            addassign.as_bytes(),
            b"begin\0end**basic string**owned\0cesu"
        );
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

        let err = Cesu8Str::from_cesu8(TEST_DATA, Variant::Standard)
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

        // actual UTF-8 error should report the first UTF-8 error in the string - the first one
        let utf8_err = err
            .utf8_error()
            .expect_err("invalid UTF-8 should set utf8_error");
        assert_eq!(
            Some(1),
            utf8_err.error_len(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );
        assert_eq!(
            0,
            utf8_err.valid_up_to(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );

        // test proper string internal assertions are still held
        let valid = Cesu8Str::from_cesu8(&TEST_DATA[..err.valid_up_to()], Variant::Standard)
            .expect("removing invalid portion should result in valid CESU-8");
        let utf8_err_valid = valid
            .utf8_error()
            .expect_err("invalid UTF-8 should set utf8_error");
        assert_eq!(
            Some(1),
            utf8_err_valid.error_len(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );
        assert_eq!(
            0,
            utf8_err_valid.valid_up_to(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );
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

        // actual UTF-8 error should report the first UTF-8 error in the string - the first one
        let utf8_err = err
            .utf8_error()
            .expect_err("invalid UTF-8 should set utf8_error");
        assert_eq!(
            Some(1),
            utf8_err.error_len(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );
        assert_eq!(
            0,
            utf8_err.valid_up_to(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );

        // test proper string internal assertions are still held
        let valid = Cesu8Str::from_cesu8(&TEST_DATA[..err.valid_up_to()], Variant::Standard)
            .expect("removing invalid portion should result in valid CESU-8");
        let utf8_err_valid = valid
            .utf8_error()
            .expect_err("invalid UTF-8 should set utf8_error");
        assert_eq!(
            Some(1),
            utf8_err_valid.error_len(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );
        assert_eq!(
            0,
            utf8_err_valid.valid_up_to(),
            "CESU-8 surrogate pair should be invalid UTF-8"
        );
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

}
