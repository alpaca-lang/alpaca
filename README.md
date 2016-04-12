mlfe
=====

ML-flavoured/fronted Erlang.

# Intentions/Goals
I want something that looks and operates a little bit like ML on the Erlang VM with:

- static typing of itself
- parametric polymorphism
- infinitely recursive functions as a distinct and allowable type for processes
looping on receive.
- recursive data types
- syntax somewhere between [OCaml](https://ocaml.org/) and
[Elm](http://elm-lang.org/), likely favouring Elm's for new data types
- FFI to erlang code that does not allow the return of values typed as `term()` or `any()`
- simple test annotations for something like
  [eunit](http://erlang.org/doc/apps/eunit/chapter.html), tests live beside the
  functions they test

The above is still a very rough and incomplete set of wishes.  In future it
might be nice to have dialyzer check the type coming back from the FFI and
suggest possible union types if there isn't an appropriate one in scope.

# FFI Thoughts
At present I'm thinking the FFI to call erlang code will take a standard
module-function-arguments tuple and a set of patterns to coerce the return into
a known type:

    type ExpectedUnion = Atom | String | Int
    type Try = Ok ExpectedUnion | Error String

    erlang_ffi (module_name, returns_term_or_atom, [a_message])
    | Atom a -> Ok a
    | String s -> Ok s
    | Int i -> Ok i
    | _ -> Error "returned something I don't know"

There's clearly room to provide a version that skips the pattern match and
succeeds if dialyzer supplies a return type for the function that matches a type
in scope (union or otherwise).

# Using It
It's not usable yet but the tests should give a relatively clear picture as to
where I'm going.

`example.mlfe` is a work in progress showing roughly what I'm aiming for.

# Parsing Approach
I'm planning on parsing/validating over several passes:

1. `yecc` for the initial rough syntax form and basic module structure.  This is
   where exports and top-level function definitions are collected and the
   initial construction of the AST is completed.
2. Validating function definitions and bindings inside of them.  This stage uses
   environments to track whether a function application is referring to a known
   function or a variable.  The output of this stage is either a module
   definition or a list of errors found.
3. Type checking.  This has some awkward overlaps with the environments built in
   the previous step and may benefit from some interleaving at some point.  An
   argument against this mixing might be that having all functions defined
   before type checking does permit forward references.

## AST Construction
Several passes internally

- for each source file (module), validate function definitions and report syntax
  errors, e.g. params that are neither unit nor variable bindings (so-called
  "symbols" from the `yecc` parser), building a list of top-level internal-only
  and exported functions for each module.  The output of this is a global
  environment containing all exported functions by module and an environment of
  top-level functions per module _or_ a list of found errors.
- for each function defined in each module, check that every variable and
  function reference is valid.  For function applications, arity is checked
  where the function applied is not in a variable.

# Type Inferencing and Checking
At present this is based off of the sound and eager type inferencer in
http://okmij.org/ftp/ML/generalization.html with some influence from
https://github.com/tomprimozic/type-systems/blob/master/algorithm_w where the
arrow type and type schema instantiation are concerned.

## Single Module Typing

    module example

    export add/2

    add x y = adder x y

    adder x y = x + y

The forward reference in `add/2` is permitted but currently leads to some wasted
work.  When typing `add/2` the typer encounters a reference to `adder/2` that is
not yet bound in its environment but is available in the module's definition.
The typer will look ahead in the module's definition to determine the type of
`adder/2`, use it to type `add/2`, and then throw that work away before
proceeding to type `adder/2` again.  It may be beneficial to leverage something
like [ETS](http://erlang.org/doc/man/ets.html) here in the near term.

## Recursion
Infinitely recursive functions are typed as such and permitted as they're
necessary for processes that loop on `receive`.  I'm presently planning on
restricting bi-directional calls between modules for simplicity.  This means
that given module `A` and `B`, calls can occur from functions in `A` to those in
`B` and vice-versa but *not* in both.

I think this is generally pretty reasonable as bidirectional references probably
indicate a failure to separate concerns but it has the additional benefit of
bounding how complicated inferencing a set of mutually recursive functions can
get.  The case I'm particularly concerned with can be illustrated with the
following `Module.function` examples:

    let A.x = B.y ()
    let B.y = C.z ()
    let C.z = A.x ()

This loop, while I belive possible to check, necessitates either a great deal of
state tracking complexity or an enormous amount of wasted work and likely has
some nasty corner cases I'm as yet unaware of.

The mechanism for preventing this is simple and relatively naive to start:
entering a module during type inferencing/checking adds that module to the list
of modules encountered in this pass.  When a call occurs (a function application
that crosses module boundaries), we check to see if the referenced module is
already in the list of entered modules.  If so, type checking fails with an
error.


# Current TODO
A somewhat structured (but unordered) set of what it will take to get to
something usable, even before worrying about tooling around dependency
management, etc.

## Missing Types

- binary
- boolean
- pid
- string
- map
- iolist
- structs
- data types (tagged unions)/ADTs

## Basic Items

- if-then-else
- inter-module calls
- basic erlang FFI
- pattern matching guards

## Receive
I think this will look like basic clauses as in matches but also requires an
optional timeout and associated action.  I'm as yet unsure of how I'm going to
handle guards on types but likely in the same way I do for the Erlang FFI.  I'm
thinking a form of predicate at the moment.

## Type Checker
Currently working for basic polymorphism and integers.  Only tested at the
per-function level.  Next key things:

- check full modules
- check inter-module calls

Longer term:

- work with the eventual Erlang FFI
- check receives

