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
hex_digit   = "0" … "9" | "a" … "f" | "A" … "F" .
octal_digit = "0" … "7" .
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
  1. *Line comments* (`LineComment`s) start with the sequence `//` and end at the next `newline`.
  2. *Block comments* (`BlockComment`s) start with the sequence `/*` and end with next occurrence of `*/`.
  3. *Documentation comments* (`DocComment`s) are line comments that start with three and only three
     slashes (`///`) instead of two (or more), as line comments might.

No type of comment can occur within a string literal ([`StringLiteral`](#string-literals)) or a
character literal ([`CharacterLiteral`](#character-literals))

### Keywords

Here is a table of keywords and their uses:
| Keyword   | Type         | Uses                             |
|-----------|--------------|----------------------------------|
| **fn**    | Declaration  | [`FnDecl`](#fn-declaration)      |
| **let**   | Declaration  | [`LetDecl`](#let-declaration)    |
| **if**    | Control flow | [`IfExpr`](#if-expression)       |
| **else**  | Control flow | [`ElseExpr`](#else-expression)   |
| **for**   | Control flow | [`ForExpr`](#for-expression)     |
| **match** | Control flow | [`MatchExpr`](#match-expression) |

TODO: More keywords should due to be added, once more has been figured out.

### Operators and Punctuation

TODO: Which operators are we going to support?

There's some punctuation that it seems like we already know - such as ',' for tuples and ';' for
statements.

This section also must list the operators that can be overloaded.

### Delimeters

Delimeters are brackets that must always be paired, and are used in various places. As such, there
are three types: Parenthesis (`(` `)`), curly braces (`{` `}`), and square brackets (`[`, `]`).
More information on the first two can be found in their respective sections:
[tuple expressions](#tuple-expression) and [block expressions](#block-expression). The third is
used for indexing, as described [here](#operators-and-punctuation).

### Values and Tuples

(Feel free to move this where it most makes sense, also, I'm aware that this has caused broken links.

Every value in TrenchCoat is in fact a tuple. There is no difference between 1, (1), or ((1)) for example. A tuple can also hold multiple values such as (1, 2, "hello").

```
StatementList = OWS Statement OWS [ ";" StatementList ]
Tuple = "(" StatementList { "," StatementList } ")"
CurlyBlock = "{" StatementList "}"
Indexer = "[" StatementList { "," StatementList } "]"
```

TODO: Define the values of tuples and curlyblocks

### Indentifiers

\[**Subject to debate**\]

TODO: General idea will be that identifiers are only valid ascii letters/numbers/underscores.
There shouldn't be any reason to have other unicode values as identifiers.

[Rust's take on identifiers](https://doc.rust-lang.org/stable/reference/identifiers.html)

[Go's take on identifiers](https://golang.org/ref/spec#Identifiers)

### Literals

```
Literal = IntegerLiteral | FloatLiteral | StringLiteral | CharacterLiteral .
```

#### Integer literals

Broadly, there are four types of integer literals: hexadecimal, decimal, octal, and binary. The
format of each of these is given by the following BNF:

```
IntegerLiteral = DecimalLiteral | HexLiteral | OctalLiteral | BinaryLiteral .

DecimalLiteral = ( "0" | ( ( "1" … "9" ) { [ "_" ] ( "0" … "9" ) } ) ) [ "_" ] IntegerType .
HexLiteral     = "0x" [ "_" ] hex_digit     { [ "_" ] hex_digit     } [ "_" ] IntegerType .
OctalLiteral   = "0o" [ "_" ] octal_digit   { [ "_" ] octal_digit   } [ "_" ] IntegerType .
BinaryLiteral  = "0b" [ "_" ] ( "0" | "1" ) { [ "_" ] ( "0" | "1" ) } [ "_" ] IntegerType .

IntegerType = TODO
```

where `IntegerType` is a suffix to specify the type of the value. Note that decimal literals cannot
contain a leading `0` as part of a larger literal. This removes any possible ambiguity surrounding
C-era octal literals, which are declared with leading zeroes.

Negation is not specified here, as it not strictly part of the literal because it results from the
unary negation operator: `-`.

All of the standard integer types are available, so:

#### Floating-point literals

Floating-point literals are as expected. Unlike integer literals, there is only one kind:

```
FloatLiteral = ( "0" | { "0" … "9" } ) [ "_" ]
               [ "." ( "0" … "9" ) { "_" | "0" … "9" } ]
               [ ( "e" | "E" ) [ "+" | "-" ] ( "1" … "9" ) { "0" … "9" } ]
```

TODO: Explain this

#### String literals

There are both "normal" string literals and raw string literals. These both function as would
be expected in many other languages, and evaluate at compile-time to a `&'static str`.

```
StringLiteral    = <"> { unicode_char | ByteEscape | UnicodeEscape | CharEscape } <"> .
RawStringLiteral = "`" { unicode_char } "`" .
```

where escapes are any one of *byte escapes* (`ByteEscape`), *unicode escapes* (`UnicodeEscape`),
or *character escapes* (`CharEscape`) - of which a handlful exist.

```
ByteEscape    = "\x" hex_digit hex_digit .
UnicodeEscape = "\u{" { hex_digit } "}" .
CharEscape    = "\" ( "n" | "r" | "t" | "\" | "0" | <"> | "'" ) .
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
| `\"`   | 0x22       | Double-quote     |
| `\'`   | 0x27       | Single-quote     |

A case for removing the vertical tab:
[https://prog21.dadgum.com/76.html](https://prog21.dadgum.com/76.html)

#### Character literals

A [character](#characters) constitutes a single unicode scalar value, and so character literals
allow values within those ranges. All of the escapes available from
[string literals](#string-literals) are available here.

```
CharacterLiteral = "'" ( unicode_char | ByteEscape | UnicodeEscape | CharEscape ) "'" .
```

Character literals evaluate to a `char`.

### Fn Declaration
A fn declaration is used to define a function, for example:
```
  fn f(x) => ...  (where ... is an `expression`)
```
Types can be specifically annotated and multiple arguments passed with:
```
  fn f(x: u32, y: u16) -> u64 => ...
```
specifying a function which takes a tuple of 1 u32 and 1 u16, and returns a tuple of 1 u64 (note that a tuple and a single item are no different).
When generic types are used, the syntax becomes:
```
  fn f<T: SomeTrait>(x: T) -> T => ...
```
To define a function which, for a type implementing the trait `T`, takes a value of type `T` and returns a value of type `T`.

