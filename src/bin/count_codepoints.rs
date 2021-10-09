use std::collections::VecDeque;
use std::io::{self, Read};
use std::fs::File;
use std::str::Utf8Error;

macro_rules! cow {
	($e: expr) => {
		std::borrow::Cow::from($e)
	};
}

#[derive(Default, Clone, Copy, Debug)]
struct Counters {
	len4: usize,
	len3: usize,
	len2: usize,
	ascii: usize,
	nul: usize,
}
impl Counters {
	fn count(chunk: &[u8]) -> Counters {
		let mut counts = Counters::default();
		for b in chunk {
			// if we aren't on a continuation byte
			if b & 0b11_00_0000 != 0b10_00_0000 {
				match *b {
					// 0 => counts.nul += 1,
					b if b               == 0b0000_0000 => counts.nul += 1,
					b if b & 0b1000_0000 == 0b0000_0000 => counts.ascii += 1,
					b if b & 0b1110_0000 == 0b1100_0000 => counts.len2 += 1,
					b if b & 0b1111_0000 == 0b1110_0000 => counts.len3 += 1,
					b if b & 0b1111_1000 == 0b1111_0000 => counts.len4 += 1,
					b => unreachable!("found non-continuation byte that is not nul/ascii/len(2,3,4)-utf8 char: {:x?}", b),
				}
			}
		}
		if chunk.len() != counts.bytes() {
			match std::str::from_utf8(chunk) {
				Ok(_) => panic!("failed to accurately count byte types for valid UTF-8 file (total = {}, calculated = {})", chunk.len(), counts.bytes()),
				Err(_) => {
					eprintln!("invalid UTF-8 passed, converting string to lossy UTF-8. Count may be off (current chunk byte count off by {})", chunk.len() as isize - counts.bytes() as isize);
				},
			}
		}
		
		// breaks if a chunk doesn't end in valid UTF-8
		counts
	}
	fn chars(&self) -> usize {
		self.len4 + self.len3 + self.len2 + self.ascii + self.nul
	}
	fn bytes(&self) -> usize {
		self.len4 * 4
		+ self.len3 * 3
		+ self.len2 * 2
		+ self.ascii
		+ self.nul
	}
	fn as_json(&self) -> String {
		format!("{{ \"nul\": {}, \"ascii\": {}, \"len2\": {}, \"len3\": {}, \"len4\": {} }}",
		        self.nul,   self.ascii,   self.len2,   self.len3,   self.len4)
	}
}
impl std::ops::Add<Counters> for Counters {
	type Output = Counters;
	
	#[inline]
	fn add(self, rhs: Counters) -> Counters {
		Counters {
			len4: self.len4 + rhs.len4,
			len3: self.len3 + rhs.len3,
			len2: self.len2 + rhs.len2,
			ascii: self.ascii + rhs.ascii,
			nul: self.nul + rhs.nul,
		}
	}
}
impl std::ops::AddAssign<Counters> for Counters {
	#[inline]
	fn add_assign(&mut self, rhs: Counters) {
		*self = *self + rhs;
	}
}
impl<'b> std::ops::AddAssign<&'b [u8]> for Counters {
	fn add_assign(&mut self, rhs: &'b [u8]) {
		*self = *self + Counters::count(rhs)
	}
}

fn main() {
	let exit_code = real_main();
	std::process::exit(exit_code);
}

fn real_main() -> i32 {
	// skip bin name
	let mut opts: VecDeque<_> = std::env::args().collect();
	let exe = opts.pop_front().map(|s| cow!(s)).unwrap_or_else(|| cow!("count_bytes"));

	if opts.iter().any(|s| s == "--help") {
		eprintln!("USAGE: {:?} [--json] [file] [KB_chunk_size=4]", exe);
		eprintln!();
		eprintln!("Reads a file and emits the number of occurences differing lengths of UTF-8 codepoints on stdout.");
		eprintln!();
		eprintln!("If `file` is not supplied, stdin will be read.");
		eprintln!();
		eprintln!("Exit Codes:");
		eprintln!("0\tSuccess");
		eprintln!("1\tCommand-line error");
		eprintln!("2\tIO Error");
		return 1;
	}

	let output_json = if let Some(i) = opts.iter().position(|s| &*s == "--json") {
		let _ = opts.remove(i).unwrap();
		true
	} else {
		false
	};

	let fname = opts.pop_front();

	let chunk_size: Option<usize> = match opts.pop_front().map(|s| s.parse::<usize>().map_err(|e| (s, e))).transpose() {
		Ok(Some(0)) => {
			eprintln!("supplied zero-length chunk size. using default chunk size.");
			None
		},
		Ok(o) => o,
		Err((s, e)) => {
			eprintln!("USAGE: {} [--json] [file] [KB_chunk_size=4]", exe);
			eprintln!("error parsing argument `chunk_size` (provided: {:?}) as positive integer: {}", s, e);
			return 1;
		}
	};

	let chunk = chunk_size.unwrap_or(4) * 1024; // 4 KiB by default

	let count: io::Result<Result<Counters, Utf8Error>> = match fname.as_deref() {
		None | Some("-") => {
			// eprintln!("using stdin");
			let stdin = io::stdin();
			let mut stdin = stdin.lock();
			readloop(&mut stdin, chunk)
		},
		Some(fname) => {
			File::open(fname).and_then(|mut f| readloop(&mut f, chunk))
		},
	};

	match count {
		Ok(Ok(n)) if output_json => {
			println!("{}", n.as_json());
			0
		},
		Ok(Ok(n)) => {
			println!("len4: {}", n.len4);
			println!("len3: {}", n.len3);
			println!("len2: {}", n.len2);
			println!("ascii: {}", n.ascii);
			println!("nul: {}", n.nul);
			println!("total (chars/bytes): {}/{}", n.chars(), n.bytes());
			0
		},
		Ok(Err(e)) => {
			eprintln!("error reading input: {}", e);
			2
		},
		Err(e) =>  {
			eprintln!("error reading input: {}", e);
			2
		},
	}
}

fn _count_chunk_bytes(chunk: &[u8]) -> usize {
	chunk.iter()
		.filter(|&b| b & 0b1111_1000 == 0b1111_0000)
		.count()
}

/// Get the index of an ending, whole UTF-8 character. Assumes input is valid UTF-8.
///
/// If the chunk contains whole characters, this will be `chunk.len()`
fn assumed_utf8_chunk(total_i: usize, chunk: &[u8]) -> usize {
	if chunk.is_empty() { return 0; }

	// find first non-continuation byte, starting from end
	// return either it's index, or the end of it

	for (i, &b) in chunk.iter().enumerate().rev() {
		// return for ascii, continue on continuation bytes
		let utf_len = match b {
			b if b & 0b1000_0000 == 0b0000_0000 => return i+1, // ascii/nul
			b if b & 0b1110_0000 == 0b1100_0000 => 2, // len2
			b if b & 0b1111_0000 == 0b1110_0000 => 3, // len3
			b if b & 0b1111_1000 == 0b1111_0000 => 4, // len4
			b if b & 0b1100_0000 == 0b1000_0000 => { continue; }, // continuation
			b => unreachable!("found non-continuation byte that is not nul/ascii/len(2,3,4)-utf8 char: {:x?} (at {:x})", b, total_i + i),
		};

		// if there is enough space for the char, return after it - otherwise, return beginning of it
		if i+utf_len > chunk.len() {
			return i;
		} else {
			// note: specifically allowing (i+utf_len == chunk.len) as this should be an exclusive end index
			return i+utf_len;
		}
	}

	// zero bytes or all continuation bytes
	if chunk.is_empty() {
		0
	} else {
		// since this is a utility helper/checker program, I don't mind simply panicking on this case
		panic!("chunk only contains continuation bytes?");
	}
}

fn readloop(input: &mut dyn Read, chunk: usize) -> io::Result<Result<Counters, Utf8Error>> {
	let bufsize: usize = chunk;
	let mut summative = Counters::default();

	// 1 megabyte buffer
	let mut buf = vec![0; bufsize];
	let mut buffered = 0;
	let mut total_i = 0;

	loop {
		// eprintln!("reading, buffered = {}", buffered);
		match input.read(&mut buf[buffered..])? {
			0 => {
				break;
			},
			n => {
				// get valid section
				let valid_up_to = assumed_utf8_chunk(total_i, &buf[..buffered+n]);
				let valid = &buf[..valid_up_to];

				// if valid_up_to != buffered+n {
				// 	eprintln!("note: splitting chunk input[0x{:X}..0x{:X}] as input[0x{:X}..0x{:X}] (last bytes: {:x?})", total_i, total_i+n, total_i, total_i+valid_up_to-buffered, &buf[(buffered+n).saturating_sub(5)..buffered+n]);
				// }
				
				// count up bytes
				summative += Counters::count(valid);
				
				// put unused bytes at the beginning
				buf.copy_within(valid_up_to..buffered+n, 0);
				buffered = buffered+n - valid_up_to;
				total_i += n;
			},
		}
	}
	
	if buffered == 0 {
		Ok(Ok(summative))
	} else {
		let uerr = std::str::from_utf8(&buf[..buffered]).expect_err("if there is buffered data left, there should be a UTF-8 error of some sort");
		Ok(Err(uerr))
	}
}
