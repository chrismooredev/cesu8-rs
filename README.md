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

## License

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
[docs-url]: https://docs.io/cesu8str
[actions-badge]: https://github.com/chrismooredev/cesu8str/workflows/CI/badge.svg
[actions-url]: https://github.com/chrismooredev/cesu8str/actions?query=workflow%3ACI+branch%3Amaster
[wikipedia-cesu8]: https://en.wikipedia.org/wiki/CESU-8
[wikipedia-mutf8]: https://en.wikipedia.org/wiki/UTF-8#Modified_UTF-8
[unicode-cesu8]: https://www.unicode.org/reports/tr26/tr26-2.html
