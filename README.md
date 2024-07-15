<div align="center">
<h1> Contra </h1>

A friendly, functional language for finding counterexamples!

[![tests](https://github.com/SophieBosio/contra/actions/workflows/tests.yaml/badge.svg)](https://github.com/SophieBosio/contra/actions/workflows/tests.yaml)
[![HLint](https://github.com/SophieBosio/contra/actions/workflows/hlint.yaml/badge.svg)](https://github.com/SophieBosio/contra/actions/workflows/hlint.yaml)

</div>
<br>

## Features

Contra is a small functional programming language designed to automate the process of finding algebraic counter-examples with property-based testing.

With Contra, you can define properties and check them automatically without the need to write a generator by hand. In particular, can check properties that take *user-defined* algebraic data types. Even mutually recursive ones!

Contra uses SMT solvers (currently Z3 via the Haskell library [SBV](https://hackage.haskell.org/package/sbv)) behind the scenes to actually find the counterexamples.

Its main contribution, and the reason you might find using Contra to be easier than using QuickCheck or SBV directly, is that Contra has a completely regular ML-style syntax, which is purposefully similar to Haskell's, and you don't need to learn any special syntax to get started.

Note that the interpreter and REPL support recursive functions, but the property-checker (using SMT solving) does not.

> [!TIP]
> This repo includes a file `contra/app/MainPretty.hs` which is a version of Contra that uses Unicode symbols. This is prettier, but not supported by all terminals. If you do have Unicode support where you plan to run Contra, you can build and install as normal, but use the executable called `contra-pretty` instead of `contra`. If you want the executable to be simply `contra`, you can rename the target executables in `./package.yaml` before building.

## Prerequisites

You need to have both the SMT solver [Z3](https://github.com/Z3Prover/z3) and the Haskell build tool [Stack](https://docs.haskellstack.org/en/stable/
"Stack") installed.

## Building, Testing, & Installing

With Z3 and Stack installed, you can clone the repo, using either HTTPS or SSH:

``` shell
# with HTTPS:
git clone https://github.com/SophieBosio/contra.git

# with SSH:
git clone git@github.com:SophieBosio/contra.git
```

Navigate to the cloned `contra` repository.

**Build** with Stack, optionally using the `--pedantic` flag:

```shell
stack build
```

**Test** with Stack, optionally using the `--pedantic` flag:

```shell
stack test
```

**Install** with Stack:

```shell
stack install
```

This should install an executable called `contra` on your system.

## Getting Started

If you're not familiar with property-based testing, there are examples
in the `./examples` folder in this repository. I can also recommend
reading John Hughes' paper [Experiences With QuickCheck: Testing the
Hard Stuff and Staying
Sane](https://link.springer.com/chapter/10.1007/978-3-319-30936-1_9).

### Checking Properties

Write a program with some properties, then, with Contra installed,
check all the properties with:

```shell
contra --check <program-name>.con
```

### Running Programs

Like a normal programming language, you can also execute Contra programs. By default, Contra looks for a function called `main` and executes it if it exists.

```shell
contra <program-name>.con
```

This prototype also comes with a rudimentary REPL. Start a blank interactive session by typing just `contra`.

Load files into the REPL with `:l <filename>.con` and quit with `:q`.

You can save function definitions (and nullary functions/constants) for the session by using the special syntax `def x = ...`.

```shell
# blank REPL session
contra
```


### Other

You can ask Contra to parse and type-check a program and print out the syntax-desugared version of your program.

```shell
# parse, type-check and print program
contra --type <program-name>.con
```

See version info.

```shell
contra --version
```

And ask to see all available options.

```shell
contra --help
```

## About

The design and implementation of Contra were part of my MSc thesis at
the University of Oslo, delivered May 15, 2024. I was supervised by Michael Kirkedal
Thomsen and Joachim Tilsted Kristensen. I'm deeply grateful to them
for their help and guidance.

The thesis text is reproduced here as a PDF at `./thesis.pdf`.

Contra is built based on the pioneering property-based testing tool, [QuickCheck](https://dl.acm.org/doi/abs/10.1145/1988042.1988046).

The underlying machinery in Contra uses the SMT solver [Z3](https://github.com/Z3Prover/z3).

The particular solver library chosen for this implementation is the Haskell
package [sbv](https://hackage.haskell.org/package/sbv).

# TODO

Suggested extensions and improvements after thesis delivery:


**Minor:**
- [ ] Pad pretty printed output to right-justify "OK"/"FAIL"/"Unknown"
- [ ] Remove the need for alpha renaming from type-inference algorithm
- [ ] Implement pretty printer for check results using Parsec instead of string manipulation

**Major:**
- [ ] Check for pattern-exhaustion in case-statements
- [ ] Support uninterpreted functions in property-checker
- [ ] (Template) polymorphism
- [ ] Termination checker
- [ ] Mode for producing different counterexamples - force SMT solver to keep producing new values
