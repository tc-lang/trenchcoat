## core

The code module is provided by the compiler, and probably does magic.

### core/prelude

The prelude module is designed to be as lightweight as possible, only including what you *really* want to be imported implicitly.

This includes primative datatypes such as intergers, floats, booleans, arrays, and a few monads.

### core/runtime

The runtime module contains the TrenchCoat runtime. This is used automatically by compiled code, although you may with to use some of its features directly.

### core/runtime/scheduler

The scheduler module contains the TrenchCoat runtimes scheduler. It is only available when enabled (usually automatically).

### core/syscall

The syscall module contains syscall wrappers that can be used by other modules.

Each function makes a raw syscall - perhaps with the runtimes scheduling wrapper around it.

### core/automic

The automic module provides automic memory primatives.

### core/sync

The sync module contains goroutine syncronisation tools, for example locks and channels.

This module may have a different implementation depending on the concurrency mode.

## ds

The ds (data structure) module provides common data structures such as vectors, maps and sets.

It is maintained by the TrenchCoat project and included in most distributions.

Sub-modules include:
- ds/vector
- ds/list
- ds/map
- ds/set
- ds/btree
- ds/tree
- ds/heap
- ds/graph
- ds/matrix
- ds/stack
- ds/queue

## string

The string module provides a string datatype, with a few helpers.

### string/encoding

The encoding module provides tools for encoding and decoding strings.

## io

The io module provides an operating system independent abstraction of IO.

Sub-modules include:
- io/fs
- io/pipe
- io/net

## net

The net module provides implementations and a framework around various network protocols.

## math

## algo

The algo module provides many standard algorithms, such as binary search, heap sort, 

## testing?

## time

## trenchcoat

The trenchcoat module is the implementation of the trenchcoat language!

### trenchcoat/parser

### trenchcoat/compiler

## os

The os module probably should be split up more than it already has been.

