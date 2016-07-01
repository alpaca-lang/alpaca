mlfe
=====
[![Build Status](https://travis-ci.org/j14159/mlfe.svg?branch=master)](https://travis-ci.org/j14159/mlfe)

ML-flavoured Erlang.

# Intentions/Goals
I want something that looks and operates a little bit like an ML on the Erlang VM with:

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
- type-safe message flows for processes defined inside MLFE

Here's an example module:

    module simple_example

    // a basic top-level function:
    add2 x = x + 2

    something_with_let_bindings x =
      // a function:
      let adder a b = a + b in
      // a variable (immutable):
      let x_plus_2 = adder x 2 in
      add2 x

    // a polymorphic ADT:
    type messages 'x = 'x | Fetch pid 'x

    /* A function that can be spawned to receive `messages int`
       messages, that increments its state by received integers
       and can be queried for its state.
    */
    will_be_a_process x = receive with
        i -> will_be_a_process (x + i)
      | Fetch sender ->
        let sent = send x sender in
        will_be_a_process x

    start_a_process init = spawn will_be_a_process [init]

# Licensing
Copyright 2016 Jeremy Pierre

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

# Contributions
Please note that this project is released with a Contributor Code of
Conduct, version 1.4. By participating in this project you agree to abide by its
terms.  See `code_of_conduct.md` for details.

Pull requests with improvements and bug reports with accompanying
tests welcome.  I'm not particularly set on syntax just yet,
especially with respect to comments.

# Using It
It's not very usable yet but the tests should give a relatively clear picture as to
where I'm going.  `test_files` contains some example source files used
in unit tests.  You can call `mlfe:compile({files,
[List, Of, File, Names, As, Strings]})` or `mlfe:compile({text,
CodeAsAString})` for now.  Errors from the compiler (e.g. type errors)
are almost comically hostile to usability at the moment.  See the
tests in `mlfe_typer.erl`.

## Prerequisites
You will generally want the following two things installed:

- Erlang R18 (I currently use [packages from Erlang Solutions](https://www.erlang-solutions.com/resources/download.html)
and haven't tested R19 yet)
- [Rebar3](https://rebar3.org)

## Writing MLFE with Rebar3
Thanks to [@tsloughter](https://github.com/tsloughter)'s
[MLFE Rebar3 plugin](https://github.com/tsloughter/rebar_prv_mlfe)
it's pretty easy to get up and running.

Make a new project with Rebar3 (substituting whatever project name
you'd like for `mlfe_example`):

    $ rebar3 new app mlfe_example
    $ cd mlfe_example

In the `rebar.config` file in your project's root folder add the
following (borrowed from @tsloughter's docs):

    {plugins, [
        {rebar_prv_mlfe, ".*", {git, "https://github.com/tsloughter/rebar_prv_mlfe.git", {branch, "master"}}}
    ]}.

    {provider_hooks, [{post, [{compile, {mlfe, compile}}]}]}.

Now any files in `src` that end with the extension `.mlfe` will be
compiled and included in Rebar3's output folders (provided they
type-check and compile successfully of course).  For a simple module,
open `src/example.mlfe` and add the following:

    module example

    export add/2

    add x y = x + y

The above is just what it looks like:  a module named `example` with a
function that adds two integers.  You can call the function directly
from the Erlang shell after compiling like this:

    $ rebar3 shell
    ... compiler output skipped ...
    1> example:add(2, 6).
    6
    2>

Note that calling MLFE from Erlang won't do any type checking but if
you've written a variety of MLFE modules in your project, all their
interactions with each other will be type checked and safe (provided
the compile succeeds).

## Compiler Hacking
If you have installed the prerequisites given above, clone this
repository and run tests and dialyzer with:

    rebar3 eunit
    rebar3 dialyzer

There's no command line front-end for the compiler so unless you use
@tsloughter's Rebar3 plugin detailed in the previous section, you will
need to boot the erlang shell and then run `mlfe:compile/1` to build
and type-check things written in MLFE.  For example, if you wanted to
compile the type import test file in the `test_files` folder:

    rebar3 shell
    ...
    1> Files = ["test_files/basic_adt.mlfe", "test_files/type_import.mlfe"].
    2> mlfe:compile({files, Files}).

This will result in either an error or a list of tuples of the following form:

    {compiled_module, ModuleName, FileName, BeamBinary}

The files will not actually be written by the compiler so the binaries
described by the tuples can either be loaded directly into the running
VM (see the tests in `mlfe.erl`) or written manually for now.

## Built-In Stuff
Most of the basic Erlang data types are supported:

- booleans, `true` or `false`
- atoms, `:atom`
- floats, `1.0`
- integers, `1`
- strings, "A string"
- lists, `[1, 2, 3]` or `1 :: 2 :: [3]`
- tuples, `("a", :tuple, "of arity", 4)`
- pids, these are parametric (like lists, "generics").  If you're
  including them in a type you can do something like `type t = int |
  pid int` for a type that covers integers and processes that receive integers.

In addition there is a unit type, expressed as `()`.

No binaries yet, see below in "What's Missing".  Note that the tuple
example above is typed as a tuple of arity 4 that requires its members
to have the types `string`, `atom`, `string`, `integer` in that order.

On top of that you can define ADTs, e.g.

    type try 'success 'error = Ok 'success | Error 'error

And ADTs with more basic types in unions work, e.g.

    type json = int | float | string | bool
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

## Processes
An example:

    f x = receive with
      (y, sender) ->
        let z = x + y in
        let sent = send z sender in
      f z

    start_f init = spawn f [init]

All of the above is type checked, including the spawn and message sends.
Any expression that contains a `receive` block becomes a "receiver"
with an associated type.  The type inferred for `f` above is the
following:

    {t_receiver,
      {t_tuple, [t_int, {t_pid, t_int}]},
      {t_arrow, [t_int], t_rec}}

This means that:

- `f` has it's own function type (the `t_arrow` part) but it _also_
  contains one or more receive calls that handle tuples of integers
  and PIDs that receive integers themselves.
- `f`'s function type is one that takes integers and is infinitely
recursive.

`send` returns `unit` but there's no "do" notation/side effect support
at the moment hence the let binding.  `spawn` for the moment can only
start functions defined in the module it's called within to simplify
some cross-module lookup stuff for the time being.  I intend to
support spawning functions in other modules fairly soon.

Note that the following will yield a type error:

    a x = receive with
      i -> b x + i

    b x = receive with
      f -> a x +. i

This is because `b` is a `t_float` receiver while `a` is a `t_int`
receiver.  Adding a union type like `type t = int | float` will solve
the type error.

If you spawn a function which nowhere in its call graph posesses a
`receive` block, the pid will be typed as `undefined`, which means
_all_ message sends to that process will be a type error.

## Current FFI
The FFI is quite limited at present and operates as follows:

    call_erlang :a_module :a_function [3, "different", "arguments"] with
       (ok, _) -> :ok
     | (error, _) -> :error

There's clearly room to provide a version that skips the pattern match and
succeeds if dialyzer supplies a return type for the function that matches a type
in scope (union or otherwise).  Worth noting that the FFI assumes you
know what you're doing and does _not_ check that the module and
function you're calling exist.


# Problems
## What's Missing
A very incomplete list:

- `self()` - it's a little tricky to type.  The type-safe solution is
  to spawn a process and then send it its own pid.  Still thinking
  about how to do this better.
- exception handling (try/catch)
- any sort of standard library.  Biggest missing things to me right
  now are things like basic string manipulation functions and
  adapters for `gen_server`, etc.
- binaries (at all).  I'm mostly thinking of just reimplementing the
  basic Erlang syntax, probably not very difficult.
- maps
- binary strings vs lists of characters, like Elixir.  I suspect
  default UTF-8 is a good decision.
- anything like behaviours or things that would support them.  Traits,
  type classes, ML modules, etc all smell like supersets to me but I'm
  not sure which way to jump yet.
- simpler FFI to Erlang via dialyzer.  I'm not certain how feasible
  this is but I'd like to dig a little deeper to see if it's
  possible.  Especially important since the FFI currently only type
  checks the results of the patterns, not the existence of the module
  and function being called, nor the arity, nor that the types of the
  provided arguments could ever ever match.
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
  collected and it's pretty trigger-happy about creating them.
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
- generalization of type variables is incompletely applied. 

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
`B` or the opposite but *not* in both directions.

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

