#![feature(trace_macros)]
#![feature(log_syntax)]

#[cfg(unix)]
mod inner_test {

use std::borrow::Cow;
use std::collections::VecDeque;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::path::PathBuf;
use std::{fs, io, fmt};
use std::fmt::Write as FmtWrite;
use std::io::{Write, Read, BufReader, BufRead, Cursor};
use std::process::{Stdio, ChildStdin, ChildStdout, Child, Output};

const UTF8: &str = "test_files/random.utf8.txt";
const CESU8: &str = "test_files/random.cesu8.txt";
const MUTF8: &str = "test_files/random.mutf8.txt";

#[derive(Debug)]
struct CodeConf {
    java: bool,
    /// decode cesu8 into utf8
    decode: bool,
}

macro_rules! emit_test_case {
    (entry) => {
        emit_test_case!(entry_rename decode, CESU8, UTF8, false, true);
        emit_test_case!(entry_rename encode, UTF8, CESU8, false, false);
        // emit_test_case!(entry_rename decode_java, MUTF8, UTF8, true, true);
        // emit_test_case!(entry_rename encode_java, UTF8, MUTF8, true, false);
    };
    (entry_rename $test_class:ident, $src: expr, $dst: expr, $java: literal, $decode: literal) => {
        paste::paste! {
            emit_test_case!(inputs [< $src:lower _to_ $dst:lower _ $test_class >], $src, $dst, $java, $decode);
        }
    };
    (inputs $iden: tt, $src: expr, $dst: expr, $java: literal, $decode: literal) => {
        // use varying input chunk sizes to test error handling/"not enough input" suppressing, around codepoint boundaries
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 1);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 2);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 3);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 4);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 5);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 6);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 7);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 16);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, chunked 256);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, fname, InputMethod::FileArg);
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, piped_explicit, InputMethod::FilePiped { explicit: true });
        emit_test_case!(inputs_rename $iden, $src, $dst, $java, $decode, piped_implicit, InputMethod::FilePiped { explicit: false });
    };
    (inputs_rename $iden: tt, $src: expr, $dst: expr, $java: literal, $decode: literal, chunked $size:literal) => {
        paste::paste! {
            emit_test_case!(outputs [< $iden _input_chunked_ $size >], $src, $dst, $java, $decode, InputMethod::FileChunked($size));
        }
    };
    (inputs_rename $iden: tt, $src: expr, $dst: expr, $java: literal, $decode: literal, $iname: ident, $imeth: expr) => {
        paste::paste! {
            emit_test_case!(outputs [< $iden _input_ $iname >], $src, $dst, $java, $decode, $imeth);
        }
    };
    (outputs $iden: tt, $src: expr, $dst: expr, $java: literal, $decode: literal, $imeth: expr) => {
        emit_test_case!(outputs_rename $iden, $src, $dst, $java, $decode, $imeth, fname, OutputMethod::FileArg);
        emit_test_case!(outputs_rename $iden, $src, $dst, $java, $decode, $imeth, piped_explicit, OutputMethod::FilePiped { explicit: true });
        emit_test_case!(outputs_rename $iden, $src, $dst, $java, $decode, $imeth, piped_implicit, OutputMethod::FilePiped { explicit: false });
    };
    (outputs_rename $iden: tt, $src: expr, $dst: expr, $java: literal, $decode: literal, $imeth: expr, $oname: ident, $ometh: expr) => {
        paste::paste! {
            emit_test_case!(finish [< $iden _output_ $oname >], $src, $dst, $java, $decode, $imeth, $ometh);
        }
    };
    (finish $iden: tt, $src: expr, $dst: expr, $java: literal, $decode: literal, $imeth: expr, $ometh: expr) => {
        ::rusty_fork::rusty_fork_test! {
            #[test]
            fn $iden() {
                let test_config = TestConfig {
                    name: stringify!($iden),
                    encoding: CodeConf { java: $java, decode: $decode, },
                    ifile: $src,
                    ofile: $dst,
                    imethod: $imeth,
                    omethod: $ometh,
                };
                eprintln!("test case: {:?}", test_config);
                test_config.test();
            }
        }
    };
}

use rusty_fork::rusty_fork_test;

#[cfg(feature = "build-binary")]
emit_test_case!(entry);

#[cfg(not(feature = "build-binary"))]
compile_error!("test binary cesu8str_converts_stdio must be build with feature 'build-binary' to be useful");

// Must enable non-blocking read for subprocess stdout or we deadlock on input of partial codepoints
// 
// Tokio feels like too heavy of a dependency to bring in just for this
// (PRs welcome for that if someone wants to develop it)
// #[cfg(any(not(unix), not(feature = "build-binary")))]
// compile_error!("unable to run cesu8str_converts_stdio test on non-unix platform without build-binary feature");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InputMethod {
    /// Command line file
    FileArg,
    /// Stdin
    FilePiped { explicit: bool },
    /// Piped into chunks based on CHUNK_SIZES
    FileChunked(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutputMethod {
    FileArg,
    /// Stdout
    FilePiped { explicit: bool },
}

trait IOHandler {
    type Method;
    fn new(id: &'static str, method: Self::Method, path: &'static str) -> Self;
    fn cmdline(&self, args: &mut Vec<Cow<'static, str>>);
    fn stdio(&mut self) -> Stdio;
    fn setup(&self, proc: &mut Child);
    fn handle(&mut self, proc: &mut Child) -> Option<bool>;
    fn finish(self, proc: &mut Child);
}

struct InputHandler {
    method: InputMethod,
    path: &'static str,
    file: Option<BufReader<fs::File>>,
}
impl IOHandler for InputHandler {
    type Method = InputMethod;
    fn new(id: &'static str, method: InputMethod, path: &'static str) -> InputHandler {
        let file = match method {
            InputMethod::FileArg => None,
            _ => {
                let f = fs::File::open(path).expect(&format!("unable to open file {:?}", path));
                Some(BufReader::new(f))
            }
        };

        InputHandler { method, path, file }
    }
    fn cmdline(&self, args: &mut Vec<Cow<'static, str>>) {
        match self.method {
            InputMethod::FileArg => args.extend_from_slice(&["--input".into(), self.path.into()]),
            InputMethod::FilePiped { explicit: true } => args.extend_from_slice(&["--input".into(), "-".into()]),
            _ => {},
        }
    }
    fn stdio(&mut self) -> Stdio {
        match self.method {
            InputMethod::FileArg => Stdio::null(),
            InputMethod::FilePiped { .. } => Stdio::from(self.file.take().unwrap().into_inner()),
            InputMethod::FileChunked(_) => Stdio::piped(),
        }
    }
    fn setup(&self, _proc: &mut Child) {
        // nothing to do - file opened in constructor
    }
    fn handle(&mut self, proc: &mut Child) -> Option<bool> {
        let chunk_size = match self.method {
            // return None when it is impossible for us to know (track process exit)
            InputMethod::FileArg => return None,
            InputMethod::FilePiped { .. } => return None,
            InputMethod::FileChunked(n) => n,
        };

        if let Some(input_file) = self.file.as_mut() {
            assert!(proc.stdin.is_some());
            input_file.fill_buf().expect(&format!("unable to read file {:?}", self.path));
            let bytes_to_write = std::cmp::min(chunk_size, input_file.buffer().len());
            if bytes_to_write == 0 { // EOF
                // drop borrow so we can take the file out of the Option to drop it
                eprintln!("input done - dropping");
                std::mem::drop(input_file);
                let input_file = self.file.take().unwrap();
                std::mem::drop(input_file); // close input file
                std::mem::drop(proc.stdin.take()); // close process stdin
                Some(true)
            } else {
                // eprintln!("trying to write {} bytes", bytes_to_write);
                let stdin = proc.stdin.as_mut().unwrap();
                match stdin.write(&input_file.buffer()[0..bytes_to_write]) {
                    Ok(n) => {
                        eprintln!(concat!("[", file!(), ":", stringify!(line!()), "] wrote {} bytes to process"), n);
                        input_file.consume(n);
                    },
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {
                        eprintln!("write interrupted");
                        /* retry on next loop */
                    },
                    Err(e) => {
                        panic!("error writing input ({} byte chunk) to cesu8str process: {:?}", bytes_to_write, e);
                    },
                };
                Some(false)
            }
        } else {
            Some(true)
        }
    }
    fn finish(self, _proc: &mut Child) {
        assert!(self.file.is_none(), "input should have dropped when done");
    }
}

#[derive(Debug)]
struct OutputHandler {
    method: OutputMethod,
    path: &'static str,
    strategy: OutputStrategy,
    blocked_in_a_row: usize,
}

// #[derive(Debug)]
enum OutputStrategy {
    File(String),
    Piped(Cursor<Vec<u8>>),
}
impl fmt::Debug for OutputStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputStrategy::File(fname) => f.write_fmt(format_args!("File({:?})", fname)),
            OutputStrategy::Piped(cursor) => f.write_fmt(format_args!("Piped {{ length={}, data={:?} }}",
                cursor.position(),
                String::from_utf8_lossy(&cursor.get_ref()[..cursor.position() as usize])
            ))
        }
    }
}

#[cfg(unix)]
impl IOHandler for OutputHandler {
    type Method = OutputMethod;
    fn new(id: &'static str, method: OutputMethod, path: &'static str) -> OutputHandler {
        let strategy: OutputStrategy = match method {
            OutputMethod::FileArg => {
                let tmpdir = env!("CARGO_TARGET_TMPDIR");
                // let t = std::time::SystemTime::now()
                //     .duration_since(std::time::SystemTime::UNIX_EPOCH)
                //     .unwrap();
                // let uniq_test_id = t.as_nanos();
                let uniq_test_id = id;
                let tmpfile = format!("{}/conversion_test.{}.txt", tmpdir, uniq_test_id);
                OutputStrategy::File(tmpfile)
            },
            OutputMethod::FilePiped { .. } => {
                let mut outputbuf: Vec<u8> = Vec::new();
                outputbuf.resize(128*1024, 0); // 128KiB - most shouldn't go over 16KiB
                let cursor = Cursor::new(outputbuf);

                OutputStrategy::Piped(cursor)
            },
        };

        OutputHandler { method, path, strategy, blocked_in_a_row: 0 }
    }
    fn cmdline(&self, args: &mut Vec<Cow<'static, str>>) {
        match self.method {
            OutputMethod::FileArg => match &self.strategy {
                OutputStrategy::File(name) => args.extend_from_slice(&["--output".into(), name.clone().into()]),
                _ => unreachable!(),
            },
            OutputMethod::FilePiped { explicit: true } => args.extend_from_slice(&["--output".into(), "-".into()]),
            OutputMethod::FilePiped { explicit: false } => {},
        }
    }
    fn stdio(&mut self) -> Stdio {
        match self.method {
            OutputMethod::FileArg => Stdio::null(),
            OutputMethod::FilePiped { .. } => Stdio::piped(),
        }
    }
    fn setup(&self, proc: &mut Child) {
        if matches!(self.method, OutputMethod::FilePiped { .. }) {
            // set IO as non-blocking
            use std::os::unix::io::AsRawFd;
            let fd = proc.stdout.as_mut().unwrap().as_raw_fd();
            unsafe {
                let res = libc::fcntl(fd, libc::F_GETFL);
                assert_ne!(res, -1, "fcntl(F_GETFL) failed: {:?}", std::io::Error::last_os_error());

                let res = libc::fcntl(fd, libc::F_SETFL, res | libc::O_NONBLOCK);
                assert_ne!(res, -1, "fcntl(F_SETFL) failed: {:?}", std::io::Error::last_os_error());
            }
        }
    }
    fn handle(&mut self, proc: &mut Child) -> Option<bool> {
        match &mut self.strategy {
            // return None when it is impossible for us to know (track process exit)
            OutputStrategy::File(_) => None,
            OutputStrategy::Piped(cursor) => {
                let remaining = cursor.get_ref().len() as u64 - cursor.position();
                eprintln!("collecting output (collected {} bytes, can consume {} more bytes)", cursor.position(), remaining);
                if remaining == 0 { panic!("test output buffer not large enough"); }
                // handle output - we should hopefully always have something here since it should have just filled
                let pos = cursor.position() as usize;
                match proc.stdout.as_mut().unwrap().read(&mut cursor.get_mut()[pos..]) {
                    Ok(0) => {
                        // EOF
                        eprintln!("read from process = EOF");
                        Some(true)
                    },
                    Ok(n) => {
                        eprintln!("read {} bytes from process", n);
                        cursor.set_position(cursor.position() + n as u64);
                        self.blocked_in_a_row = 0;
                        Some(false)
                    },
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {
                        eprintln!("read interrupted");
                        self.blocked_in_a_row = 0;
                        /* retry on next loop */
                        Some(false)
                    },
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                        // eprintln!("read would have blocked");
                        self.blocked_in_a_row += 1;
                        if self.blocked_in_a_row > 8*1024 {
                            panic!("read blocked too many times (collected {} bytes, output: strat={:?}, path={:?}, blocked={:?}, method={:?})", cursor.position(), self.strategy, self.path, self.blocked_in_a_row, self.method);
                        }
                        Some(false)
                    },
                    Err(e) => panic!("error reading output from process: {:?}", e),
                }
            }
        }
    }
    fn finish(self, _proc: &mut Child) {
        // use `differ` crate?
        match self.strategy {
            OutputStrategy::File(f) => {
                let generated = fs::read(&f).expect("error reading temporary output file");
                fs::remove_file(f).expect("error deleting temporary output file");
                let expected = fs::read(self.path).expect("error reading reference output file");
                assert_eq!(generated, expected, "generated and expected results differ (comparing output to {})", self.path);
            },
            OutputStrategy::Piped(curs) => {
                let length = curs.position();
                let mut generated = curs.into_inner();
                generated.resize(length as usize, 0);
                let expected = fs::read(self.path).expect("error reading reference output file");
                assert_eq!(generated, expected, "generated and expected results differ (comparing output to {})", self.path);
            }
        }
        
    }
}

#[cfg(unix)]
#[derive(Debug)]
struct TestConfig {
    name: &'static str,
    encoding: CodeConf,
    ifile: &'static str,
    ofile: &'static str,
    imethod: InputMethod,
    omethod: OutputMethod,
}

#[cfg(unix)]
impl TestConfig {
    fn binary() -> &'static str {
        match option_env!("CARGO_BIN_EXE_cesu8str") {
            Some(s) => s,
            None => panic!("build with --features=build-binary so cesu8str is built")
        }
    }

    fn cmdline_args(&self, input: &InputHandler, output: &OutputHandler) -> Vec<Cow<'static, str>> {
        let mut args: Vec<Cow<'static, str>> = vec![];
 
        if self.encoding.java {
            args.push("--java".into());
        }
        if self.encoding.decode {
            args.push("--decode".into());
        }

        input.cmdline(&mut args);
        output.cmdline(&mut args);
        // args.extend_from_slice(input.cmdline());
        // let output_cmdline_flags = output.cmdline();
        // args.extend(output_cmdline_flags.iter().map(|s| s.as_ref()));

        args
    }

    fn stdio_types(&self) -> (Stdio, Stdio) {
        // setup input
        let proc_stdin = match self.imethod {
            InputMethod::FileArg => Stdio::null(),
            _ => Stdio::piped(),
        };

        // setup output (possibly temp file)
        let proc_stdout = match self.omethod {
            OutputMethod::FileArg => Stdio::null(),
            OutputMethod::FilePiped { .. } => Stdio::piped(),
        };

        (proc_stdin, proc_stdout)
    }

    fn test(&self) {
        // setup IO handlers
        let mut input = InputHandler::new(self.name, self.imethod, self.ifile);
        let mut output = OutputHandler::new(self.name, self.omethod, self.ofile);

        // figure out this tests' command line flags
        let args = self.cmdline_args(&input, &output);
        eprintln!("using args: {:?}", args);
        let osargs: Vec<&OsStr> = args.iter().map(|cs| OsStr::new(cs.as_ref())).collect();

        // setup + start process
        let stdout = std::io::stdout();
        #[cfg(unix)]
        let stderr = unsafe {
            use std::os::unix::io::{AsRawFd, FromRawFd};
            Stdio::from_raw_fd(stdout.as_raw_fd())
        };
        #[cfg(windows)]
        let stderr = unsafe {
            use std::os::windows::io::{OwnedHandle, FromRawHandle, AsRawHandle};
            Stdio::from_raw_handle(stdout.as_raw_handle())
        };
        let stdio_err = Stdio::from(stderr);
        let mut proc = std::process::Command::new(TestConfig::binary())
            .stdin(input.stdio())
            .stdout(output.stdio())
            .stderr(Stdio::piped())
            .args(osargs)
            .spawn().expect("unable to create cesu8str process");

        input.setup(&mut proc);
        output.setup(&mut proc);
        let error = proc.stderr.take().unwrap();
        #[cfg(unix)] {
            // set IO as non-blocking
            use std::os::unix::io::AsRawFd;
            let fd = error.as_raw_fd();
            unsafe {
                let res = libc::fcntl(fd, libc::F_GETFL);
                assert_ne!(res, -1, "fcntl(F_GETFL) failed: {:?}", std::io::Error::last_os_error());

                let res = libc::fcntl(fd, libc::F_SETFL, res | libc::O_NONBLOCK);
                assert_ne!(res, -1, "fcntl(F_SETFL) failed: {:?}", std::io::Error::last_os_error());
            }
        }
        let mut error = BufReader::new(error);
        let mut error_read = true;
        let mut error_line = String::with_capacity(512);
        // let mut error_lines = error.lines();

        loop {
            // eprint!("(I)");
            let input_done = input.handle(&mut proc);
            // eprint!("(O)");
            let output_done = output.handle(&mut proc);
            
            while error_read {
                match error.read_line(&mut error_line) {
                    Ok(0) => {
                        eprintln!("[cesu8str] <stderr closed>");
                        error_read = false;
                    },
                    Ok(n) => {
                        eprint!("[cesu8str] {}", error_line);
                        error_line.clear();
                    },
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => { break; },
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => { break; },
                    Err(e) => panic!("encountered unknown IO error: {:?}", e),
                }
            }

            let exit_code = match (input_done, output_done) {
                (Some(false), _) => {
                    assert!(proc.try_wait().transpose().is_none(), "process exited prematurely");
                    continue
                },
                (_, Some(false)) => {
                    // assert!(proc.try_wait().transpose().is_none(), "process exited prematurely");
                    // necessary?
                    // std::thread::sleep(std::time::Duration::from_secs_f32(0.2));
                    std::thread::sleep(std::time::Duration::from_secs_f32(0.75));
                    continue
                },
                (_, _) => {
                    // we are not explicitly waiting on input/output
                    // wait for process to exit
                    eprintln!("waiting for process exit...");
                    proc.wait().expect("error waiting for process exit")
                }
            };

            eprintln!("process is done with exit code {:?} ({})", exit_code, exit_code);

            if ! exit_code.success() {
                panic!("process exited with non-zero exit code {:?}", exit_code);
            }

            break;
        }

        input.finish(&mut proc);
        output.finish(&mut proc);
        eprintln!("done");
    }
    
}

// #[test]
// fn binary_closes_gracefully_on_no_stdin() {
//     todo!("test binary with stdin as Stdio::null()");
// }

// #[test]
// fn binary_closes_gracefully_on_no_stdout() {
//     todo!("test binary with stdout as Stdio::null()");
// }

// #[test]
// fn binary_closes_gracefully_on_stdout_closure() {
//     todo!("test binary with stdout closing before end of output");
// }

}