Alpaca
=====
[![Build Status](https://travis-ci.org/alpaca-lang/alpaca.svg?branch=master)](https://travis-ci.org/alpaca-lang/alpaca)

Alpaca is a statically typed, strict/eagerly evaluated, functional programming language for the Erlang virtual machine (BEAM).  At present it relies on type inference but does provide a way to add type specifications to top-level function and value bindings.  It was formerly known as ML-flavoured Erlang (MLFE).

# TLDR; How Do I Use It?
Make sure the following are installed:

- Erlang OTP 19.3 or above ([packages from Erlang Solutions](https://www.erlang-solutions.com/resources/download.html), most development at present uses OTP 19.3 and 20.0 locally from [kerl](https://github.com/kerl/kerl))
- [Rebar3](https://rebar3.org)
- a build of Alpaca itself

## Installing Alpaca
Releases for OTP 19.3 and 20.0 are built by Travis CI and are [available under this repository's releases page here](https://github.com/alpaca-lang/alpaca/releases).  You will want one of the following:

- `alpaca_19.3.tgz`
- `alpaca_20.0.tgz`

You can unpack these anywhere and point the environment variable `ALPACA_ROOT` at the base folder, or place the `beams` sub-folder in any of the following locations:

- `/usr/lib/alpaca`
- `/usr/local/lib/alpaca`
- `/opt/alpaca`

Please see the [rebar3 plugin documentation](https://github.com/alpaca-lang/rebar_prv_alpaca) for more details.

## Using Alpaca in a Project
Make a new project with `rebar3 new app your_app_name` and in the
`rebar.config` file in your project's root folder
(e.g. `your_app_name/rebar.config`) add the following:

```erlang
{plugins, [
    {rebar_prv_alpaca, ".*", {git, "https://github.com/alpaca-lang/rebar_prv_alpaca.git", {branch, "master"}}}
]}.

{provider_hooks, [{post, [{compile, {alpaca, compile}}]}]}.
```

Check out
[the tour for the language basics](https://github.com/alpaca-lang/alpaca/blob/master/Tour.md),
put source files ending in `.alp` in your source folders, run `rebar3
compile` and/or `rebar3 eunit`.

# Building and Using Your Own Alpaca
Rather than using an official build, you can build and test your own version of Alpaca.  Please note that Alpaca now needs itself in order to build.  The basic steps are:

- Clone and/or modify Alpaca to suit your needs.
- Compile your build with `rebar3 compile`.
- Make a local untagged release for your use with `bash ./make-release.sh` in the root folder of Alpaca.

Then export `ALPACA_ROOT`, e.g. in the Alpaca folder:

    export ALPACA_ROOT=`pwd`/alpaca-unversioned_`

The	rebar3 plugin should now find the Alpaca binaries you built above.

## Editor Support

Alpaca plugins are available for various editors.

- Emacs: [alpaca-mode](https://github.com/alpaca-lang/alpaca-mode)
- Vim: [alpaca_vim](https://github.com/lepoetemaudit/alpaca_vim)
- Visual Studio Code: [alpaca-vscode](https://github.com/alpaca-lang/alpaca-vscode)

# Intentions/Goals
Something that looks and operates a little bit like an ML on the Erlang VM with:

- Static typing of itself.  We're deliberately ignoring typing of Erlang
  code that calls into Alpaca.
- Parametric polymorphism
- Infinitely recursive functions as a distinct and allowable type for processes
looping on receive.
- Recursive data types
- Syntax somewhere between [OCaml](https://ocaml.org/) and
[Elm](http://elm-lang.org/)
- FFI to Erlang code that does not allow the return of values typed as `term()` or `any()`
- Simple test annotations for something like
  [eunit](http://erlang.org/doc/apps/eunit/chapter.html), tests live beside the
  functions they test

The above is still a very rough and incomplete set of wishes.  In future it
might be nice to have dialyzer check the type coming back from the FFI and
suggest possible union types if there isn't an appropriate one in scope.

## What Works Already

- Type inferencer with ADTs.  Tuples, maps, and records for product types and
  unions for sum.  Please note that Alpaca's records are not compatible with Erlang records as the former are currently compiled to maps.
- Compile type-checked source to `.beam` binaries
- Simple FFI to Erlang
- Type-safe message flows for processes defined inside Alpaca

Here's an example module:

```elm
module simple_example

-- a basic top-level function:
let add2 x = x + 2

let something_with_let_bindings x =
  -- a function:
  let adder a b = a + b in
  -- a variable (immutable):
  let x_plus_2 = adder x 2 in
  add2 x

-- a polymorphic ADT:
type messages 'x = 'x | Fetch pid 'x

{- A function that can be spawned to receive `messages int`
    messages, that increments its state by received integers
    and can be queried for its state.
-}
let will_be_a_process x = receive with
    i -> will_be_a_process (x + i)
  | Fetch sender ->
    let sent = send x sender in
    will_be_a_process x

let start_a_process init = spawn will_be_a_process init
```

# Licensing
Alpaca is released under the terms of the Apache License, Version 2.0

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

# Contributions and Help
Please note that this project is released with a Contributor Code of
Conduct, version 1.4. By participating in this project you agree to abide by its
terms.  See `code_of_conduct.md` for details.

You can join `#alpaca-lang` on [freenode](http://freenode.net) to discuss the
language (directions, improvement) or get help.  This IRC channel is
governed by the same code of conduct detailed in this repository.

Pull requests with improvements and bug reports with accompanying
tests welcome.

# Using It
It's still quite early in Alpaca's evolution but the tests should give a relatively clear picture as to where we're going.  `test_files` contains some example source files used in unit tests.  You can call
`alpaca:compile({files, [List, Of, File, Names, As, Strings]}, [list, of, options])` or `alpaca:compile({text, CodeAsAString}, [options, again])` for now but generally we recommend using the rebar3 plugin.

Supported options are:
* `'test'` - This option will cause all tests in a module to be type checked and exported
    as functions that  [EUnit](http://erlang.org/doc/apps/eunit/chapter.html) should pick up.
* `{'warn_exhaustiveness', boolean()}` - If set to true (the default), the compiler will print warnings regarding missed patterns in top level functions.

Errors from the compiler (e.g. type errors)
are almost comically hostile to usability at the moment.  See the
tests in `alpaca_typer.erl`.

## Prerequisites
You will generally want the following two things installed:

- Erlang/OTP 19.3 or above ([packages from Erlang Solutions](https://www.erlang-solutions.com/resources/download.html), most development so far uses OTP 19.3 and 20.0 locally from [kerl](https://github.com/kerl/kerl))
- [Rebar3](https://rebar3.org)

## Writing Alpaca with Rebar3
Thanks to [@tsloughter](https://github.com/tsloughter)'s
[Alpaca Rebar3 plugin](https://github.com/alpaca-lang/rebar_prv_alpaca)
it's pretty easy to get up and running.

Make a new project with Rebar3 (substituting whatever project name
you'd like for `alpaca_example`):

    $ rebar3 new app alpaca_example
    $ cd alpaca_example

In the `rebar.config` file in your project's root folder add the
following (borrowed from @tsloughter's docs):

```erlang
{plugins, [
    {rebar_prv_alpaca, ".*", {git, "https://github.com/alpaca-lang/rebar_prv_alpaca.git", {branch, "master"}}}
]}.

{provider_hooks, [{post, [{compile, {alpaca, compile}}]}]}.
```

Now any files in the project's source folders that end with the
extension `.alp` will be compiled and included in Rebar3's output
folders (provided they type-check and compile successfully of course).
For a simple module, open `src/example.alp` and add the following:

```elm
module example

export add/2

let add x y = x + y
```

The above is just what it looks like:  a module named `example` with a
function that adds two integers.  You can call the function directly
from the Erlang shell after compiling like this (note alpaca prepends `alpaca_` to the module name, so in the erlang shell you must explicitly add this):

    $ rebar3 shell
    ... compiler output skipped ...
    1> alpaca_example:add(2, 6).
    8
    2>

Note that calling Alpaca from Erlang won't do any type checking but if
you've written a variety of Alpaca modules in your project, all their
interactions with each other will be type checked and safe (provided
the compile succeeds).

## Compiler Hacking
If you have installed the prerequisites given above, clone this
repository and run tests and dialyzer with:

    rebar3 eunit
    rebar3 dialyzer

There's no command line front-end for the compiler so unless you use
@tsloughter's Rebar3 plugin detailed in the previous section, you will
need to boot the erlang shell and then run `alpaca:compile/2` to build
and type-check things written in Alpaca.  For example, if you wanted to
compile the type import test file in the `test_files` folder:

    rebar3 shell
    ...
    1> Files = ["test_files/basic_adt.alp", "test_files/type_import.alp"].
    2> alpaca:compile({files, Files}, []).

This will result in either an error or a list of tuples of the following form:

    {compiled_module, ModuleName, FileName, BeamBinary}

The files will not actually be written by the compiler so the binaries
described by the tuples can either be loaded directly into the running
VM (see the tests in `alpaca.erl`) or written manually for now unless of
course you're using the aforementioned rebar3 plugin/

## Built-In Stuff
Most of the basic Erlang data types are supported:

- booleans, `true` or `false`
- atoms, `:atom`, `:"Quoted Atom!"`
- floats, `1.0`
- integers, `1`
- strings, `"A string"`.  These are encoded as UTF-8 binaries.
- character lists, like default Erlang strings, `c"characters here"`
- lists, `[1, 2, 3]` or `1 :: 2 :: [3]`
- binaries, `<<"안녕, this is some UTF-8 text": type=utf8>>`, `<<1, 2,
  32798: type=int, size=16, signed=false>>`, etc
- tuples, `("a", :tuple, "of arity", 4)`
- maps (basic support), e.g. `#{:atom_key => "string value"}`.  These
are statically typed as lists are (generics, parametric polymorphism).
- records (basic support), these look a bit like OCaml and Elm records, e.g. `{x=1, hello="world"}` will produce a record with an `x: int` and `hello: string` field.  Please see the  [language tour](https://github.com/alpaca-lang/alpaca/blob/master/Tour.md) for more details.
- pids, these are also parametric (like lists, "generics").  If you're
  including them in a type you can do something like `type t = int |
  pid int` for a type that covers integers and processes that receive integers.

In addition there is a unit type, expressed as `()`.

Note that the tuple example above is typed as a tuple of arity 4 that
requires its members to have the types `string`, `atom`, `string`,
`integer` in that order.

On top of that you can define ADTs, e.g.

```elm
type try 'success 'error = Ok 'success | Error 'error
```

And ADTs with more basic types in unions work, e.g.

```elm
type json = int | float | string | bool
          | list json
          | list (string, json)
```

Types start lower-case, type constructors upper-case.

Integer and float math use different symbols as in OCaml, e.g.

```elm
1 + 2      -- ok
1.0 + 2    -- type error
1.0 + 2.0  -- type error
1.0 +. 2.0 -- ok
```

Basic comparison functions are in place and are type checked, e.g. `>`
and `<` will work both in a guard and as a function but:

```elm
1 > 2             -- ok
1 < 2.0           -- type error
"Hello" > "world" -- ok
"a" > 1           -- type error
```

See `src/builtin_types.hrl` for the included functions.

## Pattern Matching
Pretty simple and straightforward for now:

```elm
let length l = match l with
    [] -> 0
  | h :: t -> 1 + (length t)
  ```

The first clause doesn't start with `|` since it's treated like a
logical OR.

Pattern match guards in clauses essentially assert types, e.g. this
will evaluate to a `t_bool` type:

```elm
match x with
  b, is_bool b -> b
```

and

```elm
match x with
  (i, f), is_integer i, is_float f -> :some_tuple
```

will type to a tuple of `integer`, `float`.

Since strings are currently compiled as UTF-8 Erlang binaries, only the first clause will ever match:

```elm
type my_binary_string_union = binary | string

match "Hello, world" with
    b, is_binary b -> b
  | s, is_string s -> s
```

Further, nullary type constructors are encoded as atoms and unary
constructors in tuples led by atoms, e.g.

```elm
type my_list 'x = Nil | Cons ('x, my_list 'x)
```

`Nil` will become `'Nil'` after compilation and `Cons (1, Nil)` will
become `{'Cons', {1, 'Nil'}}`.  Exercise caution with the order of
your pattern match clauses accordingly.

### Maps
No distinction is made syntactically between map literals and map
patterns (`=>` vs `:=` in Erlang), e.g

```elm
match my_map with
  #{:a_key => some_val} -> some_val
```

You can of course use variables to match into a map so you could write
a simple get-by-key function as follows:

```elm
type my_opt 'a = Some 'a | None

let get_by_key m k =
  match m with
      #{k => v} -> Some v
    | _ -> None
```


## Modules (The Erlang Kind)
ML-style modules aren't implemented at present.  For now modules in Alpaca are the same as
modules in Erlang with top-level entities including:

- a module name (required)
- function exports (with arity, as in Erlang)
- type imports (e.g. `use module.type`)
- type declarations (ADTs)
- functions which can contain other functions and variables via `let`
bindings.
- functions are automatically curried (with some limitations)
- simple test definitions

An example:

```elm
module try

export map/2  -- separate multiple exports with commas

-- type variables start with a single quote:
type maybe_success 'error 'ok = Error 'error | Success 'ok

-- Apply a function to a successful result or preserve an error.
let try_map e f = match e with
    Error _ -> e
  | Success ok -> Success (f ok)
```


### Tests
Tests are expressed in an extremely bare-bones manner right now and
there aren't even proper assertions available.  If the compiler is
invoked with options `[test]`, the following will synthesize and
export a function called `add_2_and_2_test`:

```elm
let add x y = x + y

test "add 2 and 2" =
  let res = add 2 2 in
  assert_equal res 4

let assert_equal x y =
  match x == y with
    | true -> :ok
    | _ -> throw (:not_equal, x, y)
```


Any test that throws an exception will fail so the above would work
but if we replaced `add/2` with `add x y = x + (y + 1)` we'd get a
failing test.  If you use the rebar3 plugin mentioned above, `rebar3
eunit` should run the tests you've written.  There's a bug currently
where the very first test run _won't_ execute the tests but all runs
after will (not sure why yet).

The expression that makes up a test's body is type inferenced and
checked.  Type errors in a test will always cause a compilation error.

## Processes
An example:

```elm
let f x = receive with
  (y, sender) ->
    let z = x + y in
    let sent = send z sender in
  f z

let start_f init = spawn f init
```


All of the above is type checked, including the spawn and message sends.
Any expression that contains a `receive` block becomes a "receiver"
with an associated type.  The type inferred for `f` above is the
following:

```erlang
{t_receiver,
  {t_tuple, [t_int, {t_pid, t_int}]},
  {t_arrow, [t_int], t_rec}}
```


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

```elm
let a x = receive with
  i -> b x + i

let b x = receive with
  f -> a x +. i
```


This is because `b` is a `t_float` receiver while `a` is a `t_int`
receiver.  Adding a union type like `type t = int | float` will solve
the type error.

If you spawn a function which nowhere in its call graph posesses a
`receive` block, the pid will be typed as `undefined`, which means
_all_ message sends to that process will be a type error.

## Current FFI
The FFI is quite limited at present and operates as follows:

```elm
beam :a_module :a_function [3, "different", "arguments"] with
    (ok, _) -> :ok
  | (error, _) -> :error
```


There's clearly room to provide a version that skips the pattern match and
succeeds if dialyzer supplies a return type for the function that matches a type
in scope (union or otherwise).  Worth noting that the FFI assumes you
know what you're doing and does _not_ check that the module and
function you're calling exist.

# Localization
Compiler error messages may be localized by calling `alpaca_error_format:fmt/2`.
If no translation is available in the specified locale, the translation for
en_US will be used.

Localization is performed using gettext ".po" files stored in priv/lang. To add
a new language, say Swedish (sv_SE), create a new file priv/lang/alpaca.sv_SE.po.
If you use Poedit, you may then import all messages to be translated by selecting
"Catalog -> Update from POT file..." in the menu, and then pick priv/lang/alpaca.pot.
The messages may be a bit cryptic. Use the en_US as an aid to understand them.

The POT file is automatically updated whenever alpaca is compiled. Updates to
po-files are also picked up at the compile phase.

# Problems
## What's Missing
A very incomplete list:

- `self()` - it's a little tricky to type.  The type-safe solution is
  to spawn a process and then send it its own pid.  Still thinking
  about how to do this better.
- exception handling (try/catch)
- any sort of standard library.  Biggest missing things right
  now are things like basic string manipulation functions and
  adapters for `gen_server`, etc.
- anything like behaviours or things that would support them.  Traits,
type classes, ML modules, etc all smell like supersets but we don't have a
definite direction yet.
- simpler FFI, there's an open issue for discussion:  https://github.com/alpaca-lang/alpaca/issues/7
- annotations in the BEAM file output (source line numbers, etc).  Not
  hard based on what can be seen in the [LFE](https://github.com/lfe)
  code base.
- support for typing anything other than a raw source file.
- type annotations/restrictions/ascriptions.  Toying with the idea
  of putting these in comments so that if the documentation is wrong
  it yields a compiler error.
- anonymous functions
- side effects, like using `;` in OCaml for printing in a function
  with a non-unit result.

## Implementation Issues
This has been a process of learning-while-doing so there are a number of issues with
the code, including but not limited to:

- reference cells in the typer are processes that are never garbage
  collected and it's pretty trigger-happy about creating them.
- there's a lot of cruft around error handling that should all be
  refactored into some sort of basic monad-like thing.  This is
  extremely evident in `alpaca_ast_gen.erl` and `alpaca_typer.erl`.  Frankly
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

```elm
module example

export add/2

let add x y = adder x y

let adder x y = x + y
```

The forward reference in `add/2` is permitted but currently leads to some wasted
work.  When typing `add/2` the typer encounters a reference to `adder/2` that is
not yet bound in its environment but is available in the module's definition.
The typer will look ahead in the module's definition to determine the type of
`adder/2`, use it to type `add/2`, and then throw that work away before
proceeding to type `adder/2` again.  It may be beneficial to leverage something
like [ETS](http://erlang.org/doc/man/ets.html) here in the near term.

## Recursion
Infinitely recursive functions are typed as such and permitted as they're
necessary for processes that loop on `receive`.  Bi-directional calls between modules
are disallowed for simplicity.  This means that given module `A` and `B`, calls
can occur from functions in `A` to those in `B` or the opposite but *not* in
both directions.

I think this is generally pretty reasonable as bidirectional references probably
indicate a failure to separate concerns but it has the additional benefit of
bounding how complicated inferencing a set of mutually recursive functions can
get.  The case I'm particularly concerned with can be illustrated with the
following `Module.function` examples:

```elm
let A.x = B.y ()
let B.y = C.z ()
let C.z = A.x ()
```

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
