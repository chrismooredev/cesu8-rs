
use std::io::{ErrorKind, Read, Write};
use std::fs::File;
use std::ops::Range;
use std::ffi::OsString;
use std::borrow::Cow;

use cesu8::Cesu8Str;
use clap::Clap;

// / Converts files or standard io streams between standard UTF8 and CESU8, or the JVM's modified UTF-8.
// / 
// / Note that the default Windows' console does not support non-UTF8 sequences - attempting to type/print them will result in an error.
// / 
// / This tool will immediately exit upon finding an invalid character sequence.
// / 
// / # Exit Code
// / `0` if operation has completed normally
// / 
// / `1` if an IO error has occured.
// / 
// / `2` if an encoding error has occured (invalid/incomplete character sequences/etc)
//asd

const HELP_TEXT: &str = "Converts files or standard IO streams between standard UTF8 and CESU8, or the JVM's modified UTF-8.
Note that the default Windows' console does not support non-UTF8 sequences - attempting to type/print them will result in an error.

This tool will immediately exit upon finding an invalid character sequence.

EXIT CODES:
0 - if completed normally
1 - if an IO error has occured
2 - if an encoding error has occured (invalid/incomplete character sequences/etc)
";

#[derive(Debug, clap::Clap)]
#[clap(version = env!("CARGO_PKG_VERSION"), author = env!("CARGO_PKG_AUTHORS"), about = HELP_TEXT)]
struct Opts {
    /// Toggles the use of the JVM's modified UTF8. In effect, it encodes nul-bytes as 0xC0,0x80 while nul-bytes are left alone in normal mode.
    #[clap(short, long)]
    java: bool,
    /// Decodes CESU8 text into standard UTF8. By default, this tool encodes UTF8 to CESU8.
    #[clap(short, long)]
    decode: bool,
    /// The input file. Defaults to stdin if '-' or not set
    input: Option<OsString>,
    /// The output file. Defaults to stdout if '-' or not set
    output: Option<OsString>,
}

const BUFSIZE: usize = 4*1024;
const EXITCODE_SUCCESS: i32 = 0;
const EXITCODE_ERROR_IO: i32 = 1;
const EXITCODE_ERROR_ENCODING: i32 = 2;

fn main() {
    let exit_code = real_main();
    std::process::exit(exit_code)
}

fn real_main() -> i32 {
    let opts = Opts::parse();

    // take input in a loop, output it
    // if either input or output is closed unexpectedly, exit gracefully (instead of panickreturning a pipe error or something)

    let debug_output = std::env::var("CESU_DEBUG").is_ok();

    let h_stdin = std::io::stdin();
    let h_stdout = std::io::stdout();

    let mut input: Box<dyn Read> = match opts.input {
        Some(file) if file.to_str() != Some("-") => {
            // we are a custom file, also not "-"
            let file = match File::open(file) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("error while opening input file for reading:");
                    eprintln!("{:?}", e);
                    return EXITCODE_ERROR_IO;
                }
            };
            Box::new(file)
        },
        _ => {
            Box::new(h_stdin.lock())
        }
    };
    
    let mut output: Box<dyn Write> = match opts.output {
        Some(file) if file.to_str() != Some("-") => {
            // we are a custom file, also not "-"
            let file = match File::create(file) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("error while creating output file for writing:");
                    eprintln!("{:?}", e);
                    return EXITCODE_ERROR_IO;
                }
            };
            Box::new(file)
        },
        _ => {
            Box::new(h_stdout.lock())
        }
    };

    // our raw buffer
    let mut rawbuf = Box::new([0u8; BUFSIZE]);
    
    // active data within our rawbuf
    let mut bounds: Range<usize> = Range { start: 0, end: 0 };

    // index of data within the file, for error reporting
    let mut absolute_start = 0;

    // if we should no longer read from the input file
    let mut reached_eof = false;

    let mut output_buffer: Vec<u8> = Vec::with_capacity(BUFSIZE);

    loop {

        // if stdin hasn't closed, and we have over 1/4 of our buffer available to fill
        if !reached_eof && (rawbuf.len() - bounds.end >= rawbuf.len()/4) {
            if debug_output { eprintln!("reading stdin (range {:?})", bounds); }

            // read more bytes into our buffer
            match input.read(&mut rawbuf[bounds.end..]) {
                Ok(0) => { // eof
                    reached_eof = true;
                },
                Ok(n) => {
                    assert!(bounds.end + n <= rawbuf.len(), "read more bytes than available in our buffer");
                    if debug_output { eprintln!("read {} bytes", n); }
                    bounds.end += n;
                },
                Err(e) if e.kind() == ErrorKind::BrokenPipe => { // would this ever happen?
                    // the pipe was broken - treat it as eof
                    reached_eof = true;
                },
                Err(e) => {
                    // unexpected error
                    eprintln!("unexpected input error, clearing output buffer and exiting.");
                    eprintln!("error: {}", e);
                    reached_eof = true;
                }
            }
        } else if debug_output {
            eprintln!("not reading stdin (reached_eof = {}, range {:?})", reached_eof, bounds);
        }

        if debug_output { eprintln!("writing buffer (range {:?}, range starts at absolute {})", bounds, absolute_start); }

        // each branch will perform encoding/decoding as necessary, removing it's consumed bytes from `bounds`

        let output_data: Cow<[u8]> = if !opts.decode { // encode into CESU8/MUTF8
            let as_str: &str = match std::str::from_utf8(&rawbuf[bounds.clone()]) {
                Ok(s) => s, // whole string good
                Err(e) => {
                    let at = absolute_start + e.valid_up_to();
                    if let Some(error_len) = e.error_len() { // invalid UTF8 sequence (not at end)
                        eprintln!("input error: invalid utf-8 sequence of {} bytes from index {} (or 0x{:x})", error_len, at, at);
                        return EXITCODE_ERROR_ENCODING;
                    } else if !reached_eof { // unterminated UTF8, but still can read more

                        if debug_output { eprintln!("unterminated UTF8, outputting what is possible"); }

                        // could use from_utf8_unchecked if performance becomes a problem here
                        std::str::from_utf8(&rawbuf[bounds.start..bounds.start+e.valid_up_to()]).unwrap()
                    } else { // unterminated UTF8, end of input
                        eprintln!("input error: incomplete utf-8 byte sequence from index {} (or 0x{:x}) at end of input", at, at);
                        return EXITCODE_ERROR_ENCODING;
                    }
                }
            };

            assert_eq!(output_buffer.len(), 0);
            let io_err = if !opts.java {
                Cesu8Str::<false>::from_utf8_writer(as_str, &mut output_buffer)
            } else {
                Cesu8Str::<true>::from_utf8_writer(as_str, &mut output_buffer)
            };
            io_err.expect("writing to a Vec cannot fail");
            
            let encoded = Cow::Borrowed(output_buffer.as_slice());

            // move the buffer back if it is <1/4 size and starts >1/2 of it (tweak?)
            assert!(bounds.len() >= as_str.len());
            bounds.start += as_str.len(); // we've consumed this amount

            encoded
        } else { // decode to UTF8

            let byterange = &rawbuf[bounds.clone()];

            let decoded = if !opts.java {
                cesu8::from_cesu8(byterange)
            } else {
                cesu8::from_java_cesu8(byterange)
            };

            // cesu8::from_*cesu8 doesn't report an error index/length like std::str::from_utf8, so we simply must exit upon a decode failure - even if it could be solved by waiting for more bytes
            // (we could lower the consumed byte range until there is no more error... but if its at the start of the string that could take a very long time)

            let as_str: Cow<str> = match decoded {
                Ok(s) => s,
                Err(e) => {
                    let at = absolute_start + e.valid_up_to();
                    if let Some(error_len) = e.error_len() { // invalid UTF8 sequence (not at end)
                        eprintln!("input error: invalid cesu-8 sequence of {} bytes from index {} (or 0x{:x})", error_len, at, at);
                        return EXITCODE_ERROR_ENCODING;
                    } else if !reached_eof { // unterminated UTF8, but still can read more

                        if debug_output { eprintln!("unterminated CESU8, outputting what is possible"); }

                        // could use from_utf8_unchecked if performance becomes a problem here
                        if !opts.java {
                            cesu8::from_cesu8(&rawbuf[bounds.start..bounds.start+e.valid_up_to()]).unwrap()
                        } else {
                            cesu8::from_java_cesu8(&rawbuf[bounds.start..bounds.start+e.valid_up_to()]).unwrap()
                        }
                    } else { // unterminated UTF8, end of input
                        eprintln!("input error: incomplete cesu-8 byte sequence from index {} (or 0x{:x}) at end of input", at, at);
                        return EXITCODE_ERROR_ENCODING;
                    }

                // Err(_ /*cesu8::Cesu8DecodingError*/) => {
                    // eprintln!("cesu8 decoding error after (but may not be exactly at) input index {} (or 0x{:x}), exiting.", absolute_start, absolute_start);
                    // return EXITCODE_ERROR_ENCODING;
                    // TODO: make Cesu8DecodingError actually provide error index' like std::str::Utf8Error
                },
            };

            // move the buffer back if it is <1/4 size and starts >1/2 of it (tweak?)
            assert!(bounds.len() >= byterange.len());
            bounds.start += byterange.len(); // we've consumed this amount

            match as_str {
                Cow::Borrowed(s) => Cow::Borrowed(s.as_bytes()),
                Cow::Owned(s) => Cow::Owned(s.into_bytes()),
            }
        };

        match output.write_all(&output_data) {
            Ok(()) => {
                if !opts.decode {
                    assert_eq!(output_buffer.len(), output_data.len());
                    output_buffer.clear();
                }
            },
            Err(e) if e.kind() == ErrorKind::BrokenPipe => {
                // expected error if used in pipelines for head/tail/grep/etc
                return EXITCODE_SUCCESS;
            },
            Err(e) => {
                eprintln!("unexpected output error, exiting: {:?}", e);
                return EXITCODE_ERROR_IO;
            }
        };


        if debug_output { eprintln!("done writing. normalizing bounds (before {:?})", bounds); }
        if bounds.is_empty() {
            absolute_start += bounds.start;
            bounds = Range { start: 0, end: 0 };
        } else if bounds.len() <= BUFSIZE/4 && bounds.start >= BUFSIZE/2 {
            rawbuf.copy_within(bounds.clone(), 0);
            absolute_start += bounds.start;
            bounds.end = bounds.len();
            bounds.start = 0;
        }
        if debug_output { eprintln!("done writing. normalizing bounds (after {:?})", bounds); }
        
        if bounds.len() == 0 && reached_eof {
            break EXITCODE_SUCCESS;
        }
    }
}
