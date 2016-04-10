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

# Current TODO

## Basic Items
An unordered list of what it will take to get to something usable, even before
worrying about tooling around dependency management, etc:

- binaries
- booleans and if-then-else
- strings
- inter-module calls
- basic erlang FFI
- structs
- pattern matching guards
- maps
- data types (tagged unions)/ADTs

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

