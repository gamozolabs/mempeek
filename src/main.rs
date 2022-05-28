#![feature(array_chunks)]

pub mod int;
pub mod constraint;

use std::str::FromStr;
use crate::int::*;
use crate::constraint::*;
use libmem::Memory;
use rustyline::Editor;
use rustyline::error::ReadlineError;
use quoted_strings::QuotedParts;

/// Wrapper for `Result`
type Result<T> = std::result::Result<T, Error>;

/// Error type
#[derive(Debug)]
pub enum Error {
    /// Error interacting with libmem
    Memory(libmem::Error),

    /// Failed to parse a signed value
    ParseSigned(std::num::ParseIntError),

    /// Failed to parse an unsigned value
    ParseUnsigned(std::num::ParseIntError),

    /// Failed to read command
    Readline(ReadlineError),

    /// Integer truncation happened when converting a `u64` to a `usize`
    TooBig,

    /// Failed to parse a floating point value
    ParseFloat(std::num::ParseFloatError),

    /// Invalid constraint
    InvalidConstraint,

    /// Got an invalid PID on the command line
    InvalidPid(std::num::ParseIntError),

    /// An invalid expression was used
    ///
    /// Currently we just support add, sub, mul, and div. No spaces. Numbers
    /// can be any base (with the correct override)
    InvalidExpression,
}

/// Different values
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Value {
    F32(f32),
    F64(f64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
}

impl Value {
    /// Create a new (zero) value with the format specified by `chr`
    pub fn default_from_letter(chr: char) -> Value {
        // Get the value
        match chr {
            'f' => Value::F32(0.),
            'F' => Value::F64(0.),
            'b' => Value::U8(0),
            'w' => Value::U16(0),
            'd' => Value::U32(0),
            'q' => Value::U64(0),
            'B' => Value::I8(0),
            'W' => Value::I16(0),
            'D' => Value::I32(0),
            'Q' => Value::I64(0),
            _ => unreachable!(),
        }
    }

    /// Interpret the value as a `u64` through casting
    pub fn as_u64(&self) -> u64 {
        match self {
            Self::F32(x) => x.to_bits() as u64,
            Self::F64(x) => x.to_bits(),
            Self::U8 (x) => *x as u64,
            Self::U16(x) => *x as u64,
            Self::U32(x) => *x as u64,
            Self::U64(x) => *x,
            Self::I8 (x) => *x as u64,
            Self::I16(x) => *x as u64,
            Self::I32(x) => *x as u64,
            Self::I64(x) => *x as u64,
        }
    }

    /// Get number of bytes per `self`
    pub fn bytes(&self) -> usize {
        match self {
            Self::F32(_) => 4,
            Self::F64(_) => 8,
            Self::U8 (_) => 1,
            Self::U16(_) => 2,
            Self::U32(_) => 4,
            Self::U64(_) => 8,
            Self::I8 (_) => 1,
            Self::I16(_) => 2,
            Self::I32(_) => 4,
            Self::I64(_) => 8,
        }
    }

    /// Get number of bytes per `self` when `Display`ed
    pub fn display(&self) -> usize {
        match self {
            Self::F32(_) => 25,
            Self::F64(_) => 25,
            Self::U8 (_) => 2,
            Self::U16(_) => 4,
            Self::U32(_) => 8,
            Self::U64(_) => 16,
            Self::I8 (_) => 4,
            Self::I16(_) => 6,
            Self::I32(_) => 11,
            Self::I64(_) => 21,
        }
    }

    /// Update value from little-endian bytes
    pub fn from_le_bytes(&mut self, bytes: &[u8]) {
        match self {
            Self::F32(ref mut val) =>
                *val = f32::from_le_bytes(bytes.try_into().unwrap()),
            Self::F64(ref mut val) =>
                *val = f64::from_le_bytes(bytes.try_into().unwrap()),
            Self::U8 (ref mut val) =>
                *val = u8::from_le_bytes(bytes.try_into().unwrap()),
            Self::U16(ref mut val) =>
                *val = u16::from_le_bytes(bytes.try_into().unwrap()),
            Self::U32(ref mut val) =>
                *val = u32::from_le_bytes(bytes.try_into().unwrap()),
            Self::U64(ref mut val) =>
                *val = u64::from_le_bytes(bytes.try_into().unwrap()),
            Self::I8 (ref mut val) =>
                *val = i8::from_le_bytes(bytes.try_into().unwrap()),
            Self::I16(ref mut val) =>
                *val = i16::from_le_bytes(bytes.try_into().unwrap()),
            Self::I32(ref mut val) =>
                *val = i32::from_le_bytes(bytes.try_into().unwrap()),
            Self::I64(ref mut val) =>
                *val = i64::from_le_bytes(bytes.try_into().unwrap()),
        }
    }

    /// Update `self` to a new value of the same type from `s`
    pub fn update_str(&mut self, s: &str) -> Result<()> {
        match self {
            Self::F32(ref mut val) => {
                *val = f32::from_str(s).map_err(Error::ParseFloat)?;
            }
            Self::F64(ref mut val) => {
                *val = f64::from_str(s).map_err(Error::ParseFloat)?;
            }
            Self::U8 (ref mut val) => *val = parse_u8 (s)?,
            Self::U16(ref mut val) => *val = parse_u16(s)?,
            Self::U32(ref mut val) => *val = parse_u32(s)?,
            Self::U64(ref mut val) => *val = parse_u64(s)?,
            Self::I8 (ref mut val) => *val = parse_i8 (s)?,
            Self::I16(ref mut val) => *val = parse_i16(s)?,
            Self::I32(ref mut val) => *val = parse_i32(s)?,
            Self::I64(ref mut val) => *val = parse_i64(s)?,
        }

        Ok(())
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::F32(val) =>
                f.write_fmt(format_args!("{:25.6}", val)),
            Self::F64(val) =>
                f.write_fmt(format_args!("{:25.6}", val)),
            Self::U8 (val) => f.write_fmt(format_args!("{:02x}", val)),
            Self::U16(val) => f.write_fmt(format_args!("{:04x}", val)),
            Self::U32(val) => f.write_fmt(format_args!("{:08x}", val)),
            Self::U64(val) => f.write_fmt(format_args!("{:016x}", val)),
            Self::I8 (val) => f.write_fmt(format_args!("{:4}", val)),
            Self::I16(val) => f.write_fmt(format_args!("{:6}", val)),
            Self::I32(val) => f.write_fmt(format_args!("{:11}", val)),
            Self::I64(val) => f.write_fmt(format_args!("{:21}", val)),
        }
    }
}

impl std::fmt::LowerHex for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::F32(val) =>
                f.write_fmt(format_args!("{:08x}", val.to_bits())),
            Self::F64(val) =>
                f.write_fmt(format_args!("{:016x}", val.to_bits())),
            Self::U8 (val) => f.write_fmt(format_args!("{:02x}", val)),
            Self::U16(val) => f.write_fmt(format_args!("{:04x}", val)),
            Self::U32(val) => f.write_fmt(format_args!("{:08x}", val)),
            Self::U64(val) => f.write_fmt(format_args!("{:016x}", val)),
            Self::I8 (val) => f.write_fmt(format_args!("{:02x}", val)),
            Self::I16(val) => f.write_fmt(format_args!("{:04x}", val)),
            Self::I32(val) => f.write_fmt(format_args!("{:08x}", val)),
            Self::I64(val) => f.write_fmt(format_args!("{:016x}", val)),
        }
    }
}

/// A memory scanner!
struct Scan {
    /// Memory
    memory: Memory,

    /// Searches which yielded results
    matches: Vec<(Vec<Constraint>, Vec<(u64, Value)>)>,
}

impl Scan {
    /// Handle a command to the scanner
    fn handle_command(&mut self, command: &[String]) -> Result<()> {
        // Nothing to do
        if command.len() == 0 { return Ok(()); }

        match command[0].as_str() {
            "exit" | "q" | "quit" => {
                // Exit the program
                std::process::exit(0);
            }
            "h" => {
                // History, displays old query results
                if command.len() != 2 {
                    println!("h <query #>");
                    return Ok(());
                }

                // Get the query number
                let query = if command[1] == "l" {
                    // 'l' is a shortcut for "last" command
                    self.matches.len() - 1
                } else {
                    parse_usize(&command[1])?
                };
                if let Some((constraints, matches)) = self.matches.get(query) {
                    for &(addr, old) in matches.iter() {
                        // Read the new value
                        let tmp =
                            self.memory.read_slice::<u8>(addr, old.bytes())
                            .map_err(Error::Memory)?;

                        // Get the new value with the same typing as the old
                        // value
                        let mut new = old;
                        new.from_le_bytes(&tmp);

                        if old != new {
                            println!("{:016x} query: {} -> {}",
                                addr, old, new);
                        } else {
                            println!("{:016x} query: {}", addr, old);
                        }
                    }

                    println!(
                        "Query #{} had {} matches with constraints:\n{:#?}",
                        query, matches.len(), constraints);
                } else {
                    println!("No matching query");
                }
            }
            "m" => {
                // Print address maps
                if let Ok(maps) = self.memory.query_address_space() {
                    for region in maps {
                        println!("{:016x}-{:016x} {}{}{}",
                            region.base, region.end,
                            if region.r { "r" } else { " " },
                            if region.w { "w" } else { " " },
                            if region.x { "x" } else { " " });
                    }
                } else {
                    println!("Failed to query address map.");
                }
            }
            "uo" |
            "ub" | "uw" | "ud" | "uq" |
            "uB" | "uW" | "uD" | "uQ" | "uf" | "uF" => {
                // Re-query only the addresses of a previous query with new
                // constraints
                if command.len() < 3 {
                    println!("u[bwdqBWDQfF] <query #> [constraints]");
                    return Ok(());
                }

                // Create value associated with type
                let value = if command[0] == "uo" {
                    None
                } else {
                    Some(Value::default_from_letter(
                        command[0].as_bytes()[1] as char))
                };

                // Create list of constraints
                let mut constraints = Vec::new();
                for constraint in &command[2..] {
                    constraints.push(
                        Constraint::from_str_value(constraint, value)?);
                }

                // Get query ID
                let query = if command[1] == "l" {
                    self.matches.len() - 1
                } else {
                    parse_usize(&command[1])?
                };
                if let Some((_, old_matches)) = self.matches.get(query) {
                    // Search through old query matches
                    let mut matches = Vec::new();
                    for &(addr, old_value) in old_matches {
                        // Check if we have a concrete value, if not, compare
                        // against the last observed value
                        let mut value = if let Some(value) = value {
                            value
                        } else {
                            for constraint in constraints.iter_mut() {
                                constraint.update_val(old_value);
                            }

                            old_value
                        };

                        // Read the new value
                        let tmp = self.memory.read_slice::<u8>(
                            addr, value.bytes())
                            .map_err(Error::Memory)?;
                        value.from_le_bytes(&tmp);

                        // Check constraints
                        if constraints.iter().all(|x| x.check(value)) {
                            matches.push((addr, value));
                        }
                    }

                    if !matches.is_empty() {
                        println!("Got {} matches, saving as query #{:x}",
                            matches.len(), self.matches.len());
                        if matches.len() < 100 {
                            for (addr, value) in &matches {
                                println!("{:016x} {}", addr, value);
                            }
                        }
                        self.matches.push((constraints, matches));
                    } else {
                        println!("No matches.");
                    }
                } else {
                    println!("No matching query");
                }
            }
            "ss" => {
                // Search for a string
                if command.len() != 4 {
                    println!("ss <addr> <length> <string>");
                    return Ok(());
                }

                // Get the address and size
                let addr = parse_u64(&command[1])?;
                let size = parse_usize(&command[2])?;

                // Read the memory
                let tmp = self.memory.read_slice::<u8>(addr, size)
                    .map_err(Error::Memory)?;

                // String search
                tmp.windows(command[3].len()).enumerate()
                        .for_each(|(ii, window)| {
                    if window == command[3].as_bytes() {
                        println!("{:016x} {}", addr + ii as u64, command[3]);
                    }
                });
            }
            "sb" | "sw" | "sd" | "sq" |
            "sB" | "sW" | "sD" | "sQ" | "sf" | "sF" => {
                // Search for a value
                if command.len() <= 3 {
                    println!("s[bwdqBWDQfF] <addr> <length> [constraints]");
                    return Ok(());
                }

                // Get the address and size
                let addr = parse_u64(&command[1])?;
                let size = parse_usize(&command[2])?;

                // Read the memory
                let tmp = self.memory.read_slice::<u8>(addr, size)
                    .map_err(Error::Memory)?;

                // Create value associated with type
                let mut value =
                    Value::default_from_letter(
                        command[0].as_bytes()[1] as char);

                // Create list of constraints
                let mut constraints = Vec::new();
                for constraint in &command[3..] {
                    constraints.push(
                        Constraint::from_str_value(constraint, Some(value))?);
                }

                // Go through memory
                let mut matches = Vec::new();
                for (ii, chunk) in tmp.chunks_exact(value.bytes()).enumerate(){
                    // Update value
                    value.from_le_bytes(chunk);

                    // Check constraints
                    if constraints.iter().all(|x| x.check(value)) {
                        let addr = addr + ii as u64 * value.bytes() as u64;
                        matches.push((addr, value));
                    }
                }

                // If we got matches, save them off
                if !matches.is_empty() {
                    println!("Got {} matches, saving as query #{:x}",
                        matches.len(), self.matches.len());
                    if matches.len() < 100 {
                        for (addr, value) in &matches {
                            println!("{:016x} {}", addr, value);
                        }
                    }
                    self.matches.push((constraints, matches));
                } else {
                    println!("No matches.");
                }
            }
            "db" | "dw" | "dd" | "dq" |
            "dB" | "dW" | "dD" | "dQ" | "df" | "dF" =>{
                // Display memory
                if !matches!(command.len(), 2 | 3) {
                    println!("d[bwdqBWDQfF] <addr> [<number of bytes>]");
                    return Ok(());
                }

                // Get the letter used with this command and use it to create a
                // dummy expected value
                let mut value =
                    Value::default_from_letter(
                        command[0].as_bytes()[1] as char);

                // Parse integer address
                let addr = parse_u64(&command[1])?;

                // Determine number of bytes to read
                let bytes = if let Some(x) = command.get(2) {
                    parse_usize(x)?
                } else {
                    64
                };

                // Read memory
                let tmp = self.memory.read_slice::<u8>(addr, bytes)
                    .map_err(Error::Memory)?;

                // Print the new line header
                print!("\x1b[0;34m{:016x}\x1b[0m: ", addr);

                // Display all the values
                let mut output_used = 0;
                let mut iter = tmp.chunks_exact(
                    value.bytes()).map(|x| Some(x)).chain(
                    std::iter::repeat(None)).enumerate().peekable();
                while let Some((ii, val)) = iter.next() {
                    if let Some(val) = val {
                        // Print the value
                        value.from_le_bytes(val);

                        // Convert the value to a `u64` and try to use it as
                        // an address to see if it is a pointer
                        let maybe_addr = value.as_u64();
                        let valid_ptr =
                            self.memory.read::<u8>(maybe_addr).is_ok();

                        if valid_ptr {
                            print!("\x1b[0;32m{}\x1b[0m ", value);
                        } else {
                            print!("{} ", value);
                        }
                    } else {
                        // Clean
                        for _ in 0..value.display() {
                            print!("?");
                        }
                        print!(" ");
                    }

                    // Update output used for this line
                    output_used += 1;
                    let vals_per_line = 16 / value.bytes();
                    if output_used == vals_per_line {
                        // Before we make the newline, print the ASCII
                        let ascii = ii / vals_per_line * vals_per_line *
                            value.bytes();
                        for byte in tmp[ascii..].iter().take(16) {
                            if byte.is_ascii_graphic() {
                                print!("{}", *byte as char);
                            } else {
                                print!(".");
                            }
                        }
                        println!();

                        // If we have nothing more to print after this, we're
                        // done
                        if matches!(iter.peek(), Some((_, None))) {
                            return Ok(());
                        }

                        // Print the new line header
                        print!("\x1b[34m{:016x}\x1b[0m: ",
                            addr + (ii as u64 + 1) * value.bytes() as u64);

                        // Update state
                        output_used = 0;
                    }
                }
            }
            _ => {
                println!("Unknown command: {:?}", command);
            }
        }

        Ok(())
    }
}

fn main() -> Result<()> {
    // Get the arguments
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("Usage: peek <pid>");
        return Ok(());
    }

    // Get the PID
    let pid = usize::from_str_radix(&args[1], 10)
        .map_err(Error::InvalidPid)?;

    // Create a readline handler
    let mut rl = Editor::<()>::new();
    let _ = rl.load_history(".peekieboi");

    // Create a memory scanner
    let mut scan = Scan {
        memory:  Memory::pid(pid).map_err(Error::Memory)?,
        matches: Vec::new(),
    };

    // Wait for commands
    loop {
        // Get command
        let command = match rl.readline(">> ") {
            Ok(x) => x,
            Err(ReadlineError::Interrupted) => {
                // Ctrl+c
                break;
            }
            Err(x) => return Err(Error::Readline(x)),
        };
        rl.add_history_entry(command.as_str());
        let _ = rl.save_history(".peekieboi");

        // Split command
        let command = QuotedParts::from(command.trim()).collect::<Vec<_>>();
        if let Err(err) = scan.handle_command(&command) {
            println!("Failed to execute command: {:?}", err);
        }
    }

    Ok(())
}

