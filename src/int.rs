//! Integer parsing helper libraries

use crate::Error;

macro_rules! impl_expr {
    ($name:ident, $name_int:ident, $ty:ty) => {
        pub fn $name(s: &str) -> crate::Result<$ty> {
            #[derive(Clone, Copy, Debug)]
            enum Expr {
                Add,
                Sub,
                Mul,
                Div,
                Val($ty),
            }

            // Split expression into components
            let mut components = Vec::new();

            let mut cur = String::new();
            for chr in s.chars() {
                if matches!(chr, '+' | '-' | '*' | '/') {
                    // Push the current component
                    components.push(Expr::Val($name_int(&cur)?));
                    match chr {
                        '+' => components.push(Expr::Add),
                        '-' => components.push(Expr::Sub),
                        '*' => components.push(Expr::Mul),
                        '/' => components.push(Expr::Div),
                        _   => unreachable!(),
                    }
                    cur.clear();
                    continue;
                }

                cur.push(chr);
            }

            // Flush remaining data
            if !cur.is_empty() {
                components.push(Expr::Val($name_int(&cur)?));
            }

            let mut ii = 0;
            while ii < components.len().saturating_sub(2) {
                let (left, op, right) = (
                    components[ii + 0],
                    components[ii + 1],
                    components[ii + 2],
                );

                let res = match (left, op, right) {
                    (Expr::Val(l), Expr::Mul, Expr::Val(r)) =>
                        l.wrapping_mul(r),
                    (Expr::Val(l), Expr::Div, Expr::Val(r)) =>
                        l.wrapping_div(r),
                    _ => {
                        ii += 1;
                        continue;
                    }
                };

                // Replace the expression with the result
                components[ii] = Expr::Val(res);

                // Remove the operation and right side as we've "consumed" them
                components.drain(ii + 1..ii + 3);
            }
            
            let mut ii = 0;
            while ii < components.len().saturating_sub(2) {
                let (left, op, right) = (
                    components[ii + 0],
                    components[ii + 1],
                    components[ii + 2],
                );

                let res = match (left, op, right) {
                    (Expr::Val(l), Expr::Add, Expr::Val(r)) =>
                        l.wrapping_add(r),
                    (Expr::Val(l), Expr::Sub, Expr::Val(r)) =>
                        l.wrapping_sub(r),
                    _ => {
                        ii += 1;
                        continue;
                    }
                };

                // Replace the expression with the result
                components[ii] = Expr::Val(res);

                // Remove the operation and right side as we've "consumed" them
                components.drain(ii + 1..ii + 3);
            }

            match components.as_slice() {
                [Expr::Val(ret)] => Ok(*ret),
                _ => Err(Error::InvalidExpression),
            }
        }
    }
}

macro_rules! int_parse {
    ($name:ident, $name_int:ident, $ty:ty) => {
        /// Parse an integer with optional base override prefix
        pub fn $name_int(mut s: &str) -> crate::Result<$ty> {
            // Default base
            let mut base = 16;

            // Invert sign
            let mut inv = false;

            // Check for a prefix
            match s.get(0..3) {
                Some("-0x" | "-0X") => { base = 16; s = &s[3..]; inv = true; }
                Some("-0d" | "-0D") => { base = 10; s = &s[3..]; inv = true; }
                Some("-0o" | "-0O") => { base =  8; s = &s[3..]; inv = true; }
                Some("-0b" | "-0B") => { base =  2; s = &s[3..]; inv = true; }
                _ => {
                    // Check for a prefix
                    match s.get(0..2) {
                        Some("0x" | "0X") => { base = 16; s = &s[2..]; }
                        Some("0d" | "0D") => { base = 10; s = &s[2..]; }
                        Some("0o" | "0O") => { base =  8; s = &s[2..]; }
                        Some("0b" | "0B") => { base =  2; s = &s[2..]; }
                        _ => {}
                    }
                }
            }

            // Parse the integer
            <$ty>::from_str_radix(s, base).map_err(crate::Error::ParseSigned)
                .map(|x| if inv { -x } else { x })
        }

        impl_expr!($name, $name_int, $ty);
    }
}

macro_rules! uint_parse {
    ($name:ident, $name_int:ident, $ty:ty) => {
        /// Parse an integer with optional base override prefix
        pub fn $name_int(mut s: &str) -> crate::Result<$ty> {
            // Default base
            let mut base = 16;

            // Check for a prefix
            match s.get(0..2) {
                Some("0x" | "0X") => { base = 16; s = &s[2..]; }
                Some("0d" | "0D") => { base = 10; s = &s[2..]; }
                Some("0o" | "0O") => { base =  8; s = &s[2..]; }
                Some("0b" | "0B") => { base =  2; s = &s[2..]; }
                _ => {}
            }

            // Parse the integer
            <$ty>::from_str_radix(s, base).map_err(crate::Error::ParseUnsigned)
        }
        
        impl_expr!($name, $name_int, $ty);
    }
}

uint_parse!(parse_u8,    parse_u8_int,    u8);
uint_parse!(parse_u16,   parse_u16_int,   u16);
uint_parse!(parse_u32,   parse_u32_int,   u32);
uint_parse!(parse_u64,   parse_u64_int,   u64);
uint_parse!(parse_usize, parse_usize_int, usize);
int_parse!(parse_i8,     parse_i8_int,    i8);
int_parse!(parse_i16,    parse_i16_int,   i16);
int_parse!(parse_i32,    parse_i32_int,   i32);
int_parse!(parse_i64,    parse_i64_int,   i64);
int_parse!(parse_isize,  parse_isize_int, isize);

