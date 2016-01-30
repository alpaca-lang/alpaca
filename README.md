mlfe
=====

ML-flavoured/fronted Erlang.

# Intentions/Goals
I want a variant of ML on the Erlang VM with:

- static typing of itself
- syntax somewhere between [OCaml](https://ocaml.org/) and
[Elm](http://elm-lang.org/), likely favouring Elm's for new data types
- FFI to erlang code that does not allow `term()` or `any()`
- dialyzer to check the type coming back from the FFI, suggest possible union
  types if there isn't an appropriate one in scope
- simple test annotations for something like
  [eunit](http://erlang.org/doc/apps/eunit/chapter.html), tests live beside the
  functions they test

I'll flesh out this list better later, the above is a very rough and incomplete
set of ideal things.

# Using It
It's not usable yet but the tests should give a relatively clear picture as to
where I'm going.

`example.mlfe` is a work in progress showing roughly what I'm aiming for.

# Parsing Approach
I'm planning on parsing/validating over several passes:

1. `yecc` for the initial rough syntax form and basic module structure.  This is
   where exports and top-level function definitions are collected.
2. Validating function definitions and bindings inside of them.  This stage uses
   environments to track whether a function application is referring to a known
   function or a variable and further turns what would be a no-argument function
   into a variable binding in `let` forms.  The output of this stage is a
   concrete AST for the compiler later.
3. Eventual type checking.  I suspect this will have some awkward overlaps with
the environments built in the previous step.

# Current TODO
An unordered list of what it will take to get to something usable, even before
worrying about tooling around dependency management, etc (doesn't include type
checker):

- unit type/constructor
- binaries
- booleans
- strings
- inter-module calls
- basic erlang FFI
- base number type for arithmetic
- remaining arithmetic operations (*, /, %)
- structs
- pattern matching guards
- maps
- data types (tagged unions)
