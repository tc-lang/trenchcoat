# This document is aiming to set out the aims of TrenchCoat.

## The general idea

The general idea of TrenchCoat is to provide set of semantically similar languages which one can jump in to the high level language with litte or no programming experience and find it intuative and simple to learn, or someone with a high level of skill in another high level language such as Python or JavaScript could quickly become familier with it. The low level language should be familier to low level programmers, but should also not shy away from being different to others such as C or Rust. While it should learn lessons from them and aim to be famlier, designing the language well should take precedence. The main aim of the low level language is to make it easy to get into from the high level language, to be able to effortlessly use high level APIs from the low level language, and low level APIs from the high level language. This allows a project to be written in a mixture; to benifit from the speed of development at the high level and the performance of the low level for the heavy lifting - that said, the high level language should be as fast as possible, without loosing the high level of abstraction we want. TrenchCoat should be capable of building anything, from operating systems, to low level utilities, to servers, to graphical applications. This means that the low level language should have powerful (and low cost) abstractions but with the ability to go as low level as required for a variety of projects.

TrenchCoat also aims to be highly interoperable with various existing languages. The obvious one being C - many existing, super high performance, libraries are written in C, or can be exposed using the C ABI; TrenchCoat should be able to easily call these. In addition, many codebases may wish to use the performance of TrenchCoat in existing projects written in higher level languages or to be able to use TrenchCoat within a team of developers that feel more comfortable writing the less performant code on other, higher level languages. The most common of these will be Python and JavaScript (especially for web development and WASM). For these reasons, TrenchCoat aims to have effortless integration with those languages and perhaps more as time goes on.

To formalize this, and expand on more details, in the high level language, you should be able to:
- use the language, with all the benifits of inferred type safety, without having to understand, or even be aware of, the type system.
- have good quality error messages that are friendly to beginners and those from other languages
- have your code compiled! Let it be FAST!
- create programs quickly. It should be abstract enough, and provide enough tools, to create functional programs incredibly quickly, without having to think in detail about every detail.
- not have to understand references vs values - things behaving as you expect by default, but also having the ability to explicity use references/values.
- call between Python, JavaScript, or other high level languages like they are written in the same language
- call low level code as if it were high level code
- have a good learning experience if it was your first language
- quickly pick it up if coming from high-level languages such as Python or JavaScript.

In the low level language, you should be able to:
- use the abstractions provided with no hidden inefficiencies. You should know how expensive something is to do. If you want it to be garbage collected, you should specify; if you want to compare things as strings when you could have just used an enum, that'll be blatently obvious (ugh, Python!).
- write code that's as low level as C can be. You should be able to directly use a memory map, or to directly make syscalls.
- quickly learn it if you already know the high level language - it should be similar enough and the type system etc should be the same. The low level language should be the high level language, but with less implicit stuff. If you master the high level language, for example you start to fully use the type system and understand how the memory managment works, then the low level language should be trivial.
- call between C ABI functions easily (perhaps it'll even parse header files..........)

Now for the juicy stuff:
- Goroutines are FANTASTIC. They should be first class, at both the high and low level; they are essential to being able to use the language in many contexts.
- Generics are a must have, at both levels.
- All the language features should eaasily readable, not only to those who know the language, but by those who know other languages.
- Bot levels should be easy to learn. Ideally easier than Rust, but that might be hard at the low level.
- Not only should there be memory and thread safety built in, but there should be
- Security built in. You should be able to compile a program in a way in which you know that it cannot access the network, or the filesystem (or maybe only a preportion of the filesystem) - except through whitelisted modules.
- Maybe you can import a module without giving it network access or access to other features, this limits the potential for malware modules.
- Runtime errors are bad

In addition to all of this, the TrenchCoat language and all TrenchCoat developed libraries should be super well documented!

Blimey this is a lot to do.

```
In summary: TrenchCoat LL = Go + Rust
            TrenchCoat HL = Python + JavaScript + Haskell + Go + Rust/10
```



PS: It's also got to be statically typed... Obviously...

# Feature requirements

To compact what was said above, for a feature to be added to the TrechCoat language, it must meet all of the folling criteria:
- It should be easy to read both for existing TrenchCoat programmers and people coming from other languages.
- It should be done simply, making it easy to learn.
- It is memory safe (unless marked as unsafe).
- It is thread sage (unless marked otherwise).
- It does not cause runtime errors unless it REALLY has to.
- It should not vialate security features.
- It should not break the ability to call FFI functions.
- It should be compilable and reasonably efficient.
- If it can cause an error, the error message should explain the error well and make finding a solution easy.
- Not break the ability for high level and low level functions to be used interchangably.

### Specifically for the low level language

- It should not hide work being done. It should be obvious how expensive (both computationally and space) an operation is.
- Features should not differ much from the high level language. The same concepts should be used with, if possible, the same syntax.

### Specifically for the high level language

- It should either be easy enough for a beginner to learn, or you should be able to write a program without knowledge of it - only using it if you need to.
- Not break the ability to treat variables and functions from another language as first class.

