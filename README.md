# Summary

This is a small command-line tool designed to peek around memory of a running
Linux process. It also provides filtering mechanisms similar to Cheat Engine
to scan for memory of certain values.

It uses `rustyline` to maintain a history of command line arguments which is
persisted in the `.peekieboi` file. Allowing "up-arrow" to work across
different runs of the tool!

# Installing

Simply run `cargo install mempeek` to install this tool! Then invoke it by
running `mempeek <pid of process to introspect>`

# Commands

## Expression support

I've added extremely basic support for expressions of various radix as well as
add, subtract, multiply, and divide. No support for parenthesis (yet).

This allows you to use an expression like `0x13370000+0o100*4` in any argument
to a command which expects a constant value. _The default radix for numbers
is 16, thus, hex unless you use an `0b`, `0o`, or `0d` prefix_

## Types

Types may be one of the following:

- `b` - `u8`
- `w` - `u16`
- `d` - `u32`
- `q` - `u64`
- `B` - `i8`
- `W` - `i16`
- `D` - `i32`
- `Q` - `i64`
- `f` - `f32`
- `F` - `f64`

## Constraints

Constraints may be any one of the following:

- `=[val]`  - Equal to `[val]`
- `![val]`  - Not equal to `[val]`
- `>[val]`  - Greater than `[val]`
- `>=[val]` - Greater than or equal to `[val]`
- `<[val]`  - Less than `[val]`
- `<=[val]` - Less than or equal to `[val]`

Currently this only supports a few commands

## `q` | `exit` | `quit`

Exit the program

## `h <query index | l>`

Get the results from a previous memory scan. Takes the query index of the query
to retrieve. Optionally, you can use `l` in place of the query index to get the
most recent query results

## `s[bwdqBWDQfF] <addr> <length> [constraints]`

Scan memory for a value of a given type starting at `addr` for `length` bytes
using `constraints`

## `u[bwdqBWDQfFo] <query #> [constraints]`

Using the address list from a previous query, interpret the pointed-to-value as
the specified type `o` implies that the update should use the type of the
original query.

## `d[bwdqBWDQfF] <addr> [<number of bytes>]`

Dump memory interpreted as a given type for a given number of bytes

## `ss <addr> <length> <string>`

Search for a `string` in a region of memory specified by `addr` and `length`
(in bytes)

## `m`

Dump memory regions and their permissions.

# Example

![Example of mempeek](/screenshot.png)

_Green values in the dump output indicate that the value is a valid pointer
when cast to a `u64`_

