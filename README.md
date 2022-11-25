# CESU-8 encoder/decoder for Rust

[![Crates.io][crates-badge]][crates-url]
[![Docs.rs][docs-badge]][docs-url]
[![Build Status][actions-badge]][actions-url]

Convert between ordinary UTF-8 and CESU-8 ([Wikipedia][wikipedia-cesu8], [Unicode Consortium][unicode-cesu8]) encodings.

CESU-8 encodes characters outside the Basic Multilingual Plane as two
UTF-16 surrogate chacaters, which are then further re-encoded as invalid,
3-byte UTF-8 characters.  This means that 4-byte UTF-8 sequences become
6-byte CESU-8 sequences.

**Note that CESU-8 is only intended for internal use within tightly-coupled
systems, and not for data interchange.**

This encoding is sometimes needed when working with Java, Oracle or MySQL,
and when trying to store emoji, hieroglyphs, or other characters on the
Supplementary Multilingual Plane or the Supplementary Ideographic Plane.

We also support Java's [Modified UTF-8][wikipedia-mutf8] encoding, which encodes `\0`
using a multi-byte UTF-8 sequence.

# Commandline Utilities

Installing:
`cargo install cesu8str --features=build-binary`

## cesu8str
encode/decode between MUTF8/CESU8 and UTF8
```
$ cesu8str --help
Converts files or standard IO streams between standard UTF8 and CESU8, or the JVM's modified UTF-8.
Note that the default Windows' console does not support non-UTF8 sequences - attempting to type/print them will result in 
an error.

This tool will immediately exit upon finding an invalid character sequence.

EXIT CODES:
0 - if completed normally
1 - if an IO error has occured
2 - if an encoding error has occured (invalid/incomplete character sequences/etc)


Usage: cesu8str [OPTIONS] [INPUT] [OUTPUT]

Arguments:
  [INPUT]   The input file. Defaults to stdin if '-' or not set
  [OUTPUT]  The output file. Defaults to stdout if '-' or not set

Options:
  -j, --java     Toggles the use of the JVM's modified UTF8. In effect, it encodes nul-bytes as 0xC0,0x80 while nul-bytes 
are left alone in normal mode
  -d, --decode   Decodes CESU8 text into standard UTF8. By default, this tool encodes UTF8 to CESU8
  -h, --help     Print help information
  -V, --version  Print version information
```

## count_codepoints - count unicode code point lengths for UTF8/16 and friends
More of a utility tool for verifying functionality during development.
```
$ count_codepoints --help
USAGE: count_codepoints [--json] [file] [KB_chunk_size=4]

Reads a file and emits the number of occurences differing lengths of UTF-8 codepoints on stdout.

If `file` is not supplied, stdin will be read.

Exit Codes:
0       Success
1       Command-line error
2       IO Error
```

### Example output:
```
$ count_codepoints ./test_files/random.txt      
len4: 1001
len3: 1013
len2: 966
ascii: 1095
nul: 0
total (chars/bytes): 4075/10070

$ count_codepoints ./test_files/random.cesu8.txt
len4: 0
len3: 3015
len2: 966
ascii: 1095
nul: 0
total (chars/bytes): 5076/1207
```

# License

Some of this code is adapted from Rust's [`src/libcore/str.rs` file][str.rs].
This code is covered by LICENSE-RUST.txt and copyright by The Rust Project
Developers and individual Rust contributors, as described in that file.

Most code in this project was forked, and adapted from, [Eric Kidd's cesu8][emk-cesu8] crate.
That adapted code is distributed under the same terms as the original project at
time of fork.

The new code in this project is distributed under the same terms.

[str.rs]: https://github.com/rust-lang/rust/blob/master/src/libcore/str.rs
[emk-cesu8]: https://github.com/emk/cesu8-rs
[crates-badge]: https://img.shields.io/crates/v/cesu8str.svg
[crates-url]: https://crates.io/crates/cesu8str
[docs-badge]: https://img.shields.io/badge/docs.rs-cesu8str?logo=docs.rs
[docs-url]: https://docs.rs/cesu8str
[actions-badge]: https://github.com/chrismooredev/cesu8str-rs/actions/workflows/rust.yml/badge.svg
[actions-url]: https://github.com/chrismooredev/cesu8str-rs/actions/workflows/rust.yml
[wikipedia-cesu8]: https://en.wikipedia.org/wiki/CESU-8
[wikipedia-mutf8]: https://en.wikipedia.org/wiki/UTF-8#Modified_UTF-8
[unicode-cesu8]: https://www.unicode.org/reports/tr26/tr26-2.html
