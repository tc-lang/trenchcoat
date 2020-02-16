# The TrenchCoat Language Specification

### Table of Contents

- [Introduction](#introduction)
- [Notation](#notation)
- [Lexical structure](#lexical-structure)
  - [Comments](#comments)
  - [Keywords](#keywords)
  - [Operators and Punctuation](#operators-and-punctuation)
  - [Delimeters](#delimeters)
  - [Identifiers](#identifiers)
  - [Literals](#literals)
    - [Integer literals](#integer-literals)
    - [Floating-point literals](#floating-point-literals)
    - [String literals](#string-literals)
    - [Character literals](#character-literals)
- Type System
- Trait System

TODO:
- Syntax structure
  - Expressions
  - Statements (just `Expr` ';')
- Variables
- Types
- Traits

## Introduction

Like some languages, TrenchCoat comes with a specification. This serves as a technical document
which can be used as a concrete reference of the expected behavior of the implementation, serving
both to resolve ambiguity surrounding the expected behavior of the compiler and to allow for the
possibility of multiple implementations.

This does *not* serve as an introduction to the language, though the more adventurous may choose
to use it as such. Separate documents exist for that purpose.

## Notation

TODO

There are multiple different ways of doing this. Go's syntax is the most compatible with working on
this document in markdown. That can be found [here](https://golang.org/ref/spec#Notation).

If this were to be converted to a webpage (where there are better opportunities for styling), Rust's
could be better suited. That can be found [here](https://doc.rust-lang.org/stable/reference/notation.html).

(temporarily) We're just directly stealing Go's. The things we use from that are:
* `character`: Any unicode code-point, excluding the newline U+000A
* `newline`: U+000A, also known as '\n'

* Negation: `~ Expr` implies that `Expr` cannot follow

```
hex_digit = "0" … "9" | "a" … "f" | "A" … "F"
```

## Lexical structure

* [Comments](#comments)
* [Keywords](#keywords)
* [Operators and Punctuation](#operators-and-punctuation)
* [Delimeters](#delimeters)
* [Identifiers](#identifiers)
* [Literals](#literals)
  * [Integer literals](#integer-literals)
  * [Floating-point literals](#floating-point-literals)
  * [String literals](#string-literals)
  * [Character literals](#character-literals)

### Comments

There are three kinds of comments, all collectively referred to by the token `Comment`:
  1. *Line comments* (`LineComment`s) start with the sequence `//` and end at the end of the line.
  2. *Block comments* (`BlockComment`s) start with the sequence `/*` and end with a matching `*/`.
  3. *Documentation comments* (`DocComment`s) are line comments that start with three and only three
     slashes (`///`) instead of two (or more), as line comments might.

No type of comment can occur within a string literal ([`StringLiteral`](#string-literals)) or a
character literal ([`CharacterLiteral`](#character-literals))

### Keywords

Here is a table of keywords and their uses:
| Keyword   | Type         | Uses                             |
|-----------|--------------|----------------------------------|
| **fn**    | Declaration  | [`FnDecl`](#fn-declaration)      |
| **if**    | Control flow | [`IfExpr`](#if-expression)       |
| **else**  | Control flow | [`ElseExpr`](#else-expression)   |
| **for**   | Control flow | [`ForExpr`](#for-expression)     |
| **match** | Control flow | [`MatchExpr`](#match-expression) |

TODO: More keywords should due to be added, once more has been figured out.

### Operators and Punctuation

TODO: Which operators are we going to support?

There's some punctuation that it seems like we already know - such as ',' for tuples and ';' for
statements.

### Delimeters

### Indentifiers

\[**Subject to debate**\]

TODO: General idea will be that identifiers are only valid ascii letters/numbers/underscores.
There shouldn't be any reason to have other unicode values as identifiers.

[Rust's take on identifiers](https://doc.rust-lang.org/stable/reference/identifiers.html)

[Go's take on identifiers](https://golang.org/ref/spec#Identifiers)

### Literals

#### Integer literals

TODO: What'll we use for integer types? I'm inclined to follow with
[what Rust has done](https://doc.rust-lang.org/stable/reference/tokens.html#numbers), because
they're clean, clear, and simple.

#### Floating-point literals

TODO: A bit more thought should go into this - it needs to be compatible with whatever integer
syntax we choose.

#### String literals

There are both "normal" string literals and raw string literals. These both function as would
be expected in many other languages, and evaluate at compile-time to a `&'static str`.

```
StringLiteral    = TODO

RawStringLiteral = "`" { unicode_char } "`"
```

where escapes are any one of *byte escapes* (`ByteEscape`), *unicode escapes* (`UnicodeEscape`),
or *character escapes* (`CharEscape`) - of which a handlful exist.

```
ByteEscape    = "\x" hex_digit hex_digit

UnicodeEscape = "\u{" { hex_digit } "}"

CharEscape    = "\" ( "n" | "r" | "t" | "\" | "0" )
```

Note that unicdode escapes may have **at most** 6 digits, representing a code point up to 24 bytes.
A table has been placed below to give meaning to the character escapes.

| Escape | Byte-value | Meaning          |
|--------|------------|------------------|
| `\n`   | 0x0A       | Newline          |
| `\r`   | 0x0D       | Carriage-return  |
| `\t`   | 0x09       | Tab              |
| `\\`   | 0x5C       | Backslash        |
| `\0`   | 0x00       | Null / Zero byte |

A case for removing the vertical tab:
[https://prog21.dadgum.com/76.html](https://prog21.dadgum.com/76.html)

#### Character literals

TODO
