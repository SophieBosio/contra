<div align="center">
<h1> Contra </h1>

A friendly, functional language for finding counterexamples!

[![tests](https://github.com/SophieBosio/contra/actions/workflows/tests.yaml/badge.svg)](https://github.com/SophieBosio/contra/actions/workflows/tests.yaml)
[![HLint](https://github.com/SophieBosio/contra/actions/workflows/hlint.yaml/badge.svg)](https://github.com/SophieBosio/contra/actions/workflows/hlint.yaml)

</div>
<br>

## Features

Contra is a small functional programming language designed
to automate the process of finding counter-examples with
property-based testing.

With Contra, you can define properties and check them automatically
without the need to write a generator by hand. You can even check
properties containing algebraic data types.

## Building, Testing, & Installing

First, make sure you have [Stack](https://docs.haskellstack.org/en/stable/
"Stack") installed.

Then, clone the repo, using either HTTPS or SSH:

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

Write a program with some properties, then, with Contra installed,
check all the properties with:

```shell
contra --check <program-name>.con
```

## About

The design and implementation of Contra were part of my MSc thesis at
the University of Oslo, delivered 2024. I was supervised by Michael Kirkedal
Thomsen and Joachim Tilsted Kristensen. I'm deeply grateful to them
for their help and guidance.

The underlying machinery in Contra uses the pioneering property-based testing
tool,
[QuickCheck](https://dl.acm.org/doi/abs/10.1145/1988042.1988046) and
SMT solving.

The particular solver library chosen for this implementation is the Haskell
package [sbv](https://hackage.haskell.org/package/sbv).


