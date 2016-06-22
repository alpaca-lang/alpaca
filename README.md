mlfe
=====

ML-flavoured/fronted Erlang.

# Intentions/Goals
I want something that looks and operates a little bit like ML on the Erlang VM with:

- static typing of itself.  I'm deliberately ignoring typing of Erlang
  code that calls into MLFE.
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

## What Works Already

- type inferencer with ADTs.  Tuples for product types and unions for sum.
- compile type-checked source to `.beam` binaries
- simple FFI to Erlang

# Current FFI
The FFI is quite limited at present and operates as follows:

    call_erlang :a_module :a_function [3, "different", "arguments"] with
       (ok, _) -> :ok
     | (error, _) -> :error

There's clearly room to provide a version that skips the pattern match and
succeeds if dialyzer supplies a return type for the function that matches a type
in scope (union or otherwise).

# Using It
It's not very usable yet but the tests should give a relatively clear picture as to
where I'm going.  `test_files` contains some example source files used
in unit tests.  You can call `mlfe:compile({files,
[List, Of, Files]})` or `mlfe:compile({text, CodeAsAString})` for now.

## Built-In Stuff
Most of the basic Erlang data types are supported:

- booleans, `true` or `false`)
- atoms, `:atom`
- floats, `1.0`
- integers, `1`
- strings, "A string"
- lists, `[1, 2, 3]` or `1 :: 2 :: [3]`
- tuples, `("a", :tuple, "of arity", 4)`

In addition there is a unit type, expressed as `()`.

No binaries yet, see below in "What's Missing".  Note that the tuple
example above is typed as a tuple of arity 4 that requires its members
to have the types `string`, `atom`, `string`, `integer` in that order.

On top of that you can define ADTs, e.g.

    type try 'success 'error = Ok 'success | Error 'error

And ADTs with more basic types in unions work, e.g.

    type json = int | float | string | bool "
              | list json
              | list (string, json)

Types start lower-case, type constructors upper-case.

Integer and float math use different symbols as in OCaml, e.g.

    1 + 2      // ok
    1.0 + 2    // type error
    1.0 + 2.0  // type error
    1.0 +. 2.0 //ok

Basic comparison functions are in place and are type checked, e.g. `>`
and `<` will work both in a guard and as a function but:

    1 > 2             // ok
    1 < 2.0           // type error
    "Hello" > "world" // ok
    "a" > 1           // type error

See `src/builtin_types.hrl` for the included functions.

## Pattern Matching
Pretty simple and straightforward for now:

    length l = match l with
        [] -> 0
      | h :: t -> 1 + (length t)

The first clause doesn't start with `|` since it's treated like a
logical OR.

Pattern match guards in clauses essentially assert types, e.g. this
will evaluate to a `t_bool` type:

    match x with
      b, is_bool b -> b

and

    match x with
      (i, f), is_integer i, is_float f -> :some_tuple

will type to a tuple of `integer`, `float`.

Since strings are currently just lists of characters as in Erlang
proper, only the first clause will ever match:

    type my_list_string_union = list int | string

    match "Hello, world" with
        l, is_list l -> l
      | s, is_string s -> s

Further, nullary type constructors are encoded as atoms and unary
constructors in tuples led by atoms, e.g.

    type my_list 'x = Nil | Cons ('x, my_list 'x)

`Nil` will become `'Nil'` after compilation and `Cons (1, Nil)` will
become `{'Cons', {1, 'Nil'}}`.  Exercise caution with the order of
your pattern match clauses accordingly.

## Modules (The Erlang Kind)
ML-style modules aren't implemented and I'm leaning somewhat more
towards type classes and traits.  Modules in MLFE are the same as
modules in Erlang, top-level entities including:

- a module name (required)
- function exports (with arity, as in Erlang)
- type imports (e.g. `use module.type`)
- type declarations (ADTs)
- functions which can contain other functions and variables via `let`
bindings.

An example:

    module try

    export map/2  // separate multiple exports with commas

    // type variables start with a single quote:
    type maybe_success 'error 'ok = Error 'error | Success 'ok

    // Apply a function to a successful result or preserve an error.
    map e f = match e with
        Error _ -> e
      | Success ok -> Success (f ok)

# Problems
## What's Missing
A very incomplete list:

- exception handling (try/catch)
- any sort of standard library.  Biggest missing things to me right
  now are things like basic string manipulation functions and
  adapters for `gen_server`, etc.
- binaries (at all).  I'm mostly thinking of just reimplementing the
  basic Erlang syntax, probably not very difficult.
- binary strings vs lists of characters, like Elixir.  I suspect
  default UTF-8 is a good decision.
- anything like behaviours or things that would support them.  Traits,
  type classes, ML modules, etc all smell like supersets to me but I'm
  not sure which way to jump yet.
- simpler FFI to Erlang via dialyzer.  I'm not certain how feasible
  this is but I'd like to dig a little deeper to see if it's possible.
- anything for unit testing
- annotations in the BEAM file output (source line numbers, etc).  Not
  hard based on what I've seen in the [LFE](https://github.com/lfe)
  code base.
- support for typing anything other than a raw source file.  I need to
  investigate reading/writing beam file annotations to help with this
  I suspect.
- records, especially with structural matching.
- pattern matching in function declarations directly rather than in
  the body.
- type annotations/restrictions/ascriptions.  I'm toying with the idea
  of putting these in comments so that if the documentation is wrong
  it yields a compiler error.
- anonymous functions
- side effects, like using `;` in OCaml for printing in a function
  with a non-unit result.

## Implementation Issues
I've been learning-while-doing so there are a number of issues with
the code, including but not limited to:

- reference cells in the typer are processes that are never garbage
  collected.
- there's a lot of cruft around error handling that should all be
  refactored into some sort of basic monad-like thing.  This is
  extremely evident in `mlfe_ast_gen.erl` and `mlfe_typer.erl`.  Frankly
  the latter is begging for a complete rewrite.
- type unification error line numbers can be confusing.  Because of
  the sequence of unification steps, sometimes the unification error
  might occur at a function variable's location or in a match
  expression rather than in the clauses.  I'm considering tracking the
  history of changes over the course of unifications in a reference
  cell in order to provide a typing trace to the user.

# Parsing Approach
Parsing/validating occurs in several passes:

1. `yecc` for the initial rough syntax form and basic module structure.  This is
   where exports and top-level function definitions are collected and the
   initial construction of the AST is completed.
2. Validating function definitions and bindings inside of them.  This stage uses
   environments to track whether a function application is referring to a known
   function or a variable.  The output of this stage is either a module
   definition or a list of errors found.  This stage also renames
   variables internally.
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

## No "Any" Type
There is currently no "any" root/bottom type.  This is going to be a problem for
something like a simple `println`/`printf` function as a simple to use version
of this would best take a List of Any.  The FFI to Erlang code gets around this
by not type checking the arguments passed to it and only checking the result
portion of the pattern matches.

