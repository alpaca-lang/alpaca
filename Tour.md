<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#sec-1">1. Intro</a>
<ul>
<li><a href="#sec-1-1">1.1. Helpful Foundations</a></li>
<li><a href="#sec-1-2">1.2. About This Document</a></li>
</ul>
</li>
<li><a href="#sec-2">2. The Structure of a Program</a>
<ul>
<li><a href="#sec-2-1">2.1. What Modules Include</a></li>
</ul>
</li>
<li><a href="#sec-3">3. Included Data Types</a>
<ul>
<li><a href="#sec-3-1">3.1. The Basic Ones</a>
<ul>
<li><a href="#sec-3-1-1">3.1.1. Booleans</a></li>
<li><a href="#sec-3-1-2">3.1.2. Numbers</a></li>
<li><a href="#sec-3-1-3">3.1.3. Atoms</a></li>
<li><a href="#sec-3-1-4">3.1.4. Strings</a></li>
<li><a href="#sec-3-1-5">3.1.5. Binaries</a></li>
</ul>
</li>
<li><a href="#sec-3-2">3.2. The Polymorphic Ones</a>
<ul>
<li><a href="#sec-3-2-1">3.2.1. Tuples</a></li>
<li><a href="#sec-3-2-2">3.2.2. Lists</a></li>
<li><a href="#sec-3-2-3">3.2.3. Maps</a></li>
<li><a href="#sec-3-2-4">3.2.4. Records</a></li>
<li><a href="#sec-3-2-5">3.2.5. PIDs</a></li>
</ul>
</li>
</ul>
</li>
<li><a href="#sec-4">4. Functions</a>
<ul>
<li><a href="#sec-4-1">4.1. The Foreign Function Interface</a></li>
<li><a href="#sec-4-2">4.2. Built-In Functions</a></li>
<li><a href="#sec-4-3">4.3. Currying</a></li>
<li><a href="#sec-4-4">4.4. Lambdas</a></li>
</ul>
</li>
<li><a href="#sec-5">5. User Defined Types:  ADTs</a></li>
<li><a href="#sec-6">6. Tests</a></li>
<li><a href="#sec-7">7. Processes</a></li>
<li><a href="#sec-8">8. Exporting and Importing Functions</a></li>
</ul>
</div>
</div>

# Intro<a id="sec-1" name="sec-1"></a>

This document provides a tour of Alpaca's current capabilities and limitations in a bit more depth for anyone looking to use it.

Some of Alpaca's goals:

-   A statically typed, strictly evaluated (eager, not lazy), and functional language for the Erlang platform.
-   Infer types as much as possible so we only need to be explicit where it matters.
-   A reasonably flexible approach to simple Algebraic Data Types (ADTs) .
-   Interoperate with existing Erlang code and libraries as safely as possible.

## Helpful Foundations<a id="sec-1-1" name="sec-1-1"></a>

If you're unfamiliar with Erlang itself, I'd highly recommend the excellent [Learn You Some Erlang for great good!](http://learnyousomeerlang.com/)  The sections on [the basic data types](http://learnyousomeerlang.com/starting-out-for-real) and on [modules](http://learnyousomeerlang.com/modules) will probably help a great deal to start understanding where Alpaca fits and what it does.

Much of Alpaca in its current state borrows (in an unstructured manner) aspects of a number of languages that descend from [ML](https://en.wikipedia.org/wiki/ML_(programming_language)) including:

-   [OCaml](https://ocaml.org/)
-   [Haskell](https://www.haskell.org/)
-   [Elm](http://elm-lang.org/)

While you probably don't need to know any of them in detail, some of the syntax in this document might make a bit more sense if you're familiar with one of the above (including ML).

## About This Document<a id="sec-1-2" name="sec-1-2"></a>

This document is exported from the Emacs org-mode doc `Tour.org` using `org-md-export-to-markdown`.  Corrections and suggestions welcome via PRs to the main [Alpaca repository](https://github.com/alpaca-lang/alpaca).

# The Structure of a Program<a id="sec-2" name="sec-2"></a>

Alpaca at present is really just a new way to write modules for an Erlang application.

## What Modules Include<a id="sec-2-1" name="sec-2-1"></a>

The set of top-level elements permitted in a module are the following:

-   a module declaration, e.g. `module my_module_name`.  This is required.
-   function exports.  These tell the compiler which functions should be publicly accessible to modules outside of the ones we write in Alpaca.
-   type definitions.  These describe new types as ADTs.
-   test cases
-   comments, though these can go anywhere and are not restricted to the top level.
-   functions.  These can contain other functions and variables inside of them.

Here's a simple example of a module:

```elm
module my_module

-- one function that takes a single argument will be publicly accessible:
export double/1

{- Our double function defines an "add" function inside of itself.
    Comments for now are C-style.
    -}
let double x =
  let add a b = a + b in
  add x x

test "doubling 2 is 4" = some_test_checker (double 2) 4

-- Basic ADT with type constructors:
type even_or_odd = Even int | Odd int

-- A function from integers to our ADT:
let even_or_odd x =
  let rem = x % 2 in
  match rem with
  | 0 -> Even x
  | _ -> Odd x
```


Note that variables and function names follow the same format, beginning with a lower-case character.

# Included Data Types<a id="sec-3" name="sec-3"></a>

## The Basic Ones<a id="sec-3-1" name="sec-3-1"></a>

### Booleans<a id="sec-3-1-1" name="sec-3-1-1"></a>

Just `true` and `false`, not atoms as in Erlang although they're encoded as such after compilation.

### Numbers<a id="sec-3-1-2" name="sec-3-1-2"></a>

Alpaca has integers and floats which can't mix with each other at all.  They have separate arithmetic instructions as in OCaml:

```elm
1 + 2       -- integer
1.0 +. 2.0  -- float
1 +. 2      -- type error, +. is only for floats
1 +. 2.0    -- type error, can't mix integers and floats
```

### Atoms<a id="sec-3-1-3" name="sec-3-1-3"></a>

Atoms in Alpaca are just text prefixed with `:`, e.g. `:this_is_an_atom` and `:soIsThis1`. Quotes may be used if spaces or symbols are required, e.g. `:"still an atom!"`.

### Strings<a id="sec-3-1-4" name="sec-3-1-4"></a>

Strings in Alpaca are all assumed UTF-8 and will be encoded as such:

```elm
"This is a string"
"so is 한국 and 日本"
```

These are compiled as binaries under the hood.  If you're looking for Erlang's basic string types, character lists can be constructed by prefixing a string with `c`, for example:

```elm
c"character list!"
```

### Binaries<a id="sec-3-1-5" name="sec-3-1-5"></a>

If you're not familiar with binaries, there's some [good coverage](http://learnyousomeerlang.com/starting-out-for-real) of them in [Learn You Some Erlang&#x2026;](http://learnyousomeerlang.com/)  At present in Alpaca they're a little more verbose but also a little more obvious, e.g.

```elm
<<"this text is assumed to be UTF-8">>
<<"But we can also be explicit": type=utf8>>

{- endian, sign, units and size all work, here's how we might encode
  * a 32-bit, big-endian, unsigned integer:
  -}
<<SomeInteger: type=int, size=8, unit=4, end=big, sign=false>>

-- of course we can just list off integers and floats too:
<<1, 2, 3.14, 4, 5, 6.0>>
```

Endian settings can be `big`, `little`, or `native` as in Erlang.

## The Polymorphic Ones<a id="sec-3-2" name="sec-3-2"></a>

These types are all "parametrically polymorphic", or "generics" for those of us familiar with Java. This means that these types contain data of another type in a general manner so that we can have "a list of integers" and "a list of strings" without changing any of the code involving lists themselves.

### Tuples<a id="sec-3-2-1" name="sec-3-2-1"></a>

Tuples, like functions, have a specific arity (number of contained elements).  In Alpaca the typing of tuples covers both their arity **and** the type of each element.  Let's introduce pattern matching here to illustrate their structure:

```elm
let third my_tuple =
  match my_tuple with
    (_, _, x) -> x

let third_string my_tuple =
  match my_tuple with
    (_, _, x), is_string x -> x

third (1, 2, 3) -- will return the integer 3

{- The following will fail compilation with a type error because
  * third_string/1 only takes tuples that have strings as their
  * third element:
  -}
third_string (1, 2, 3)

{- Both of the following will also fail compilation since the function
  * third/1 requires tuples with exactly 3 elements:
  -}
third (1, 2)
third (1, 2, 3, 4)

{- This function will also fail to compile because tuples of arity 2
    and those of arity 3 are fundamentally different types:
  -}
let second_or_third my_tuple =
  match my_tuple with
      (_, _, x) -> x
    | (_, x) -> x
```


We can express the types of tuples with tuples themselves, for example `(int, string)` for tuples of integers and strings.

### Lists<a id="sec-3-2-2" name="sec-3-2-2"></a>

Lists compile directly to Erlang lists but of course they're type-checked. This means, for example, that we aren't able to mix integers and floats in the same list without creating an ADT that covers them both.  We can express "list of strings" with the type `list string`.

We can build lists up with the cons operator `::` or as literals:

```elm
"end" :: "a" :: "cons'd" :: "list" :: "with the nil literal []" :: []
["or just put", "it", "in", "square brackets"]

-- type error:
[:atom, "and a string"]
```


Let's revisit pattern matching here as well with both forms:

```elm
let length my_list =
  match my_list with
      [] -> 0
    | _ :: t -> 1 + (length t)

let is_length_3 my_list =
  match my_list with
      [_, _, _] -> true
    | _ -> false
```


### Maps<a id="sec-3-2-3" name="sec-3-2-3"></a>

Maps are type-checked as lists are but have separate types for their keys vs their values.  If we wanted a map with atom keys and string values, it could be expressed as the type `map atom string`.  Functionality is relatively limited still but we can construct literal maps, add single key-value pairs to maps, and pattern match on them.

```elm
#{:key => "value"}  -- a literal

{- This will cause a type error because the types of the keys
  * don't match:
  -}
#{:key1 => "value 1", "key 2" => "value 2"}
```


### Records<a id="sec-3-2-4" name="sec-3-2-4"></a>

Records can be created ad-hoc wherever you like as in OCaml and Elm and you can pattern match on the structure of records as well.

```elm
{x=1, hello="world"}  -- a literal record

-- we have basic structural matching:
match {x=1, hello="world"} with
  {x=xx} -> xx

{- We have "row polymorphism" which means that if you call the following
    function with {x=1, hello="world"}, the return type does not lose the
    information about the hello field.  The return type of calling the
    function below with that record will be (int, {x: int, hello: string}).
-}
let x_in_a_tuple my_rec =
  match my_rec with
    {x=xx} -> (xx, my_rec)
```


1.  Record Transformations

    Records can be transformed and extended with the same syntax.  Alpaca doesn't consider these "updates" since the original record never changes.  If we wanted to add fields `x` and `y` to an existing record `rec`, it's pretty straightforward:

        let a_new_record = {x=1, y=2.0 | rec}

    Note that the original record `rec` has not changed, we have made an entirely new record that contains all of the fields in the original along with our new integer `x` field and the float `y` field.

    The same syntax can be used to replace a member.  If we wanted to replace `x` in the example `a_new_record` above, here's how we'd do it:

        {x=5 | a_new_record}

    What happens if we change the type of a field?

        -- {x: int, y: int}
        let rec1 = {x=1, y=2}

        -- {x: string, y: int}
        let rec2 = {x="hello!" | rec1}

    Remember that transforming a record actually makes an entirely new one so we allow for members to change type since it's not **actually** a mutation anyhow.   Thanks to <https://github.com/danabr> for the suggestion of "transformation" rather than "update".

    There are currently no plans to enable the removal of record fields.

2.  What's Row Polymorphism?

    The key thing we're after from row polymorphism is not losing information.  For example in Java if we had the following:

        public interface IHasX {
            public int getX();
        }

        public class HasXY implements IHasX {
            public final int x;
            public final String hello;

            public HasXY(int x, String hello) {
                this.x = x;
                this.hello = hello;
            }

            public int getX() { return x; }
            public String getHello() { return hello; }
        }

        public IHasX identity(IHasX i) {
            return i;
        }

    The return of `identity(new HasXY(1, "world"))` "loses" the information that the passed-in argument has a `hello` member of type `String`.

        let identity my_rec =
          match my_rec with
            {x=_} -> my_rec

    The return of `identity({x=1, hello="world"})` above is still the type `{x: int, hello: string}` in Alpaca  even though the function `identity` only cares about the field `x: int`.

3.  What's Missing?

    There's not yet a way to access individual fields of a record without pattern matching (e.g. `let my_rec = {x=1, hello="world"} in x.x`)

### PIDs<a id="sec-3-2-5" name="sec-3-2-5"></a>

Process identifiers (references to processes to which we can send messages) are typed with the kind of messages they are able to receive.  The type of process that only knows how to receive strings can be expressed as `pid string`.  We'll cover processes and PIDs in a bit more detail later but if you're unfamiliar with them from Erlang, [The Hitchhiker's Guide to Concurrency](http://learnyousomeerlang.com/the-hitchhikers-guide-to-concurrency) from Learn You Some Erlang is a great place to start.

# Functions<a id="sec-4" name="sec-4"></a>

Inside of a function we can define both immutable variables and new functions:

```elm
let f x =
  let double y = y + y in      -- this is a single argument function
  let doubled_x = double x in  -- a variable named "double_x"
  doubled_x + x                -- the expression returned as a result
```


As Alpaca is an expression-oriented language, there are no return statements.  Just as in Erlang, the final expression in a function is the value returned to the caller.  The type of a function or variable is entirely inferred by the type checker:

```elm
{- Because the body of this function multiplies the parameter by a float,
    the compiler knows that this function takes floats and returns floats
    (float -> float).  If we were to call this function with something other
    than a float (e.g. an integer or string), the compiler would fail with
    a type error.
-}
let double x = x *. 2.0
```


Type signatures can be set on top level functions and values, e.g.:

```elm
val add : fn int int -> int
let add x y = x + y
```

The signatures look a little different to the other MLs, while resembling OCaml the most; they are consistent with Alpaca's type definitions in ADTs. Another example, demonstrating polymorphic parameters:

```
val apply 'a 'b : fn (fn 'a -> 'b) a -> 'b
let apply f x = f x
```


Note the explicit listing of type variables `'a` and `'b` after the name of the signature, and that arguments are not separated by `->` but listed simply with a space between them, with the arguments separated from the return type by a single `->`. For fairly exhaustive examples of type signatures, please see `basic_signature_test.alp` in the test suite.

Most of the time, you can safely omit type signatures. They can be useful in getting early feedback from the compiler that your types infer as you expect. They are also useful in making generic, unbounded functions and types more specific (specialization). They are essential when writing functions that wrap `beam` FFI calls, where the inputs are always unbounded, e.g:

```elm
val print_string : fn string -> unit
let print_string str =
  beam :io :put_chars [str] with
  | _ -> ()
```


By forcing `print_string` to take only strings, we guard against passing types that Erlang's `io:put_chars` can't understand, preventing a runtime error.

While functions with no arguments aren't supported ("nullary" or arity of zero) we can use the unit term `()` if we don't need or want to pass anything specific.  Let's introduce the basic foreign function interface here to call an Erlang io function:

```elm
let print_hello () =
  beam :io :format ["Hello~n", []] with _ -> ()
```


## The Foreign Function Interface<a id="sec-4-1" name="sec-4-1"></a>

The FFI is how we call any non-Alpaca code in the Erlang VM (e.g. Erlang, [Elixir](http://elixir-lang.org/), [LFE](http://lfe.io/), and more).  Since our compiler can't type-check other languages, we combine a call to another module and function with a set of pattern match clauses to figure out what the actual type is that we're returning from it.

Here we're using a simple guard function so that we know the FFI expression is returning characters (an Erlang string):

```elm
beam :io_lib :format ["This will contain the integer 3:  ~w", [3]] with
  cs, is_chars cs -> cs
```


The FFI `beam` expects the external module and function as atoms and then a list of arguments to send.  The arguments sent are **not** type checked but the return value in the pattern matching clauses **is** checked.

## Built-In Functions<a id="sec-4-2" name="sec-4-2"></a>

The basic infix comparisons are all available and can be used in pattern matching guards:

-   `==` for equality, compiles to `=:=`
-   `!=` for inequality
-   `>`, `<`, `>=`, and `<=`

Some simple examples:

```elm
1 == 1     -- true
1 == 2     -- false
1 == 1.0   -- type error
:a == :a   -- true
```


The basic arithmetic functions also exist, `+`, `-`, `*`, `/`, and `%` for modulo.  The base forms are all for integers, just add `.` to them for the float versions except for modulo (e.g. `+.` or `/.`).

Some other simple type checking functions are also usable in pattern match guards:

-   `is_integer`
-   `is_float`
-   `is_atom`
-   `is_bool`
-   `is_list`
-   `is_string`
-   `is_chars`
-   `is_pid`
-   `is_binary`

A word of caution:  strings are encoded as binaries, and chars as lists so if we call the following example `f/1` with a string, we will **always** get a binary back (assuming there's an ADT covering both):

```elm
let f x =
  match x with
      b, is_binary b -> b
    | s, is_string s -> s
```


And here we will always get a list instead of a character list (same ADT restriction):

```elm
let g x =
  match x with
      l, is_list l -> l
    | c, is_chars c -> c
```


## Currying<a id="sec-4-3" name="sec-4-3"></a>

Top level functions can be curried. Practically speaking, this means that if
you do not provide a function with all of its required arguments, it instead
returns another function that takes the remaining arguments. There are some
limitations to this:

-   If multiple versions of a function are defined, such as `f/2` and `f/3`,
    supplying a single argument to `f` would be ambiguous, so this is disallowed
-   Functions defined in `let... in...` bindings cannot (currently) be curried
-   When currying a function defined in another module, the function must first
    be explicitly imported, i.e. ~other<sub>module</sub>.my<sub>fun</sub> "hello"~ would not work,
    but ~import other<sub>module</sub>.my<sub>fun</sub>;; my<sub>fun</sub> "hello"~ would.

The latter two are limitations that should go away in future.

Some examples:

```elm
-- Currying means we can use a 'pipe forward' operator to 'chain' expressions
let (|>) x f = f x

let add a b = a + b
let sub a b = a - b

let result () =
  10 |> add 5 |> sub 2 |> add 19

-- We can create predicates for use with higher order functions, e.g.
let eq x y =
  x == y

-- assuming a filter/2 function that takens a predicate function and a list 'a
let filtered_list () =
  filter (eq 3) [1, 2, 3]
```


## Lambdas<a id="sec-4-4" name="sec-4-4"></a>

Lambdas (AKA anonymous functions) can be defined with the `fn` keyword:

```elm
fn x -> x + 1
```


They can also be bound to variable names, e.g. these two versions of `double` will produce the exact same output binary:

```elm
let double = fn x -> x + x

let double x = x + x
```


We can also use lambdas as arguments to other functions, here's an example of passing a function that adds 1 to each element of an integer list:

```elm
let example () =
  map (fn x -> x + 1) [1, 2, 3]

test "example should result in [2, 3, 4]" =
  assert_equal (example ()) [2, 3, 4]

-- here's a simple definition of the map function:
let map f [] = []
let map f (h :: t) = (f h) :: (map f t)
```


Finally, we can use the unicode lambda and right-arrow characters if we want to.  These two functions are identical:

```elm
λ x → x + 1

fn x -> x + 1
```


So the following would work the same as our `example` function above:

```elm
let example () =
  map (λ x → x + 1) [1, 2, 3]
```


# User Defined Types:  ADTs<a id="sec-5" name="sec-5"></a>

We can currently specify new types by combining existing ones, creating [algebraic data types (ADTs)](https://en.wikipedia.org/wiki/Algebraic_data_type).  These new types will also be inferred correctly, here's a simple example of a broad "number" type that combines integers and floats:

```elm
-- a union:
type number = int | float
```


We can also use "type constructors" and type variables to be a bit more expressive.  Type constructors start with an uppercase letter (e.g. `Like` `These`) and can have a single associated value.  Type variables start with a single apostrophe like 'this.  Here's a simple example of an option type that's also polymorphic/generic (like lists and maps):

```elm
{- `Some` has a single associated value, `None` stands alone.  Note that
    we have the type variable 'a here that lets us be particular about which
    items in the type's members are polymorphic.
-}
type opt 'a = Some 'a | None

{- Here's a map "get value by key" function that uses the new `opt` type.
    It's polymorphic in that if we give this function a `map string int`
    and a string for `key`, the return type will be an `opt int`.  If we
    instead give it a `map atom (list string)` and an atom for the key,
    the return type will be `opt (list string)`.
-}
let map_get key the_map =
  match the_map with
      #{key => value} -> Some value
    | _ -> None
```


We can use the basic Alpaca types as well, here's a type that describes parsed JSON data based on how the [JSX](https://github.com/talentdeficit/jsx) library represents it:

```elm
type json = int | float | string | bool
          | list json
          | list (string, json)
```


If the above type is in scope (in the module, or imported), the following function's type will be inferred as one from `json` to `atom`:

```elm
let f x =
  match x with
      i, is_integer i -> :integer
    | f, is_float f -> :float
```


If the inferencer has more than one ADT unifying integers and floats in scope, it will choose the one that occurs first.  In the following example, `f/1` will type to accepting `int_or_float` rather than `json`.

```elm
type int_or_float = int | float

type json = int | float | string | bool
          | list json
          | list (string, json)

let f x =
  match x with
      i, is_integer i -> :integer
    | f, is_float f -> :float
```


# Tests<a id="sec-6" name="sec-6"></a>

Support for tests inside source files is currently at its most basic with the goal of keeping unit tests alongside the functions they're testing directly rather than in a separate file.

Tests:

-   can occur anywhere within a module
-   are only compiled and exported if the compiler is told to run in test generation mode (the atom `test` given in its options)
-   are run by [EUnit](http://erlang.org/doc/apps/eunit/chapter.html)
-   fail if an error/exception is thrown in the test's expression

Here's a simple example:

```elm
let add x y = x + y

test "add 2 2 should result in 4" =
  add 2 2
```


While the above test is type checked and will happily be compiled, we lack assertions to actually **test** the call to add.  They can be built relatively simply for now, here's a full module example using a simple equality check from one of the test files, `basic_module_with_tests.alp`:

```elm
module add_and_a_test

export add/2

let add x y = x + y

test "add 2 2 should result in 4" = test_equal (add 2 2) 4

{- Test the equality of two terms, throwing an exception if they're
    not equal.  The two terms will need to be the same type for any
    call to this to succeed:
  -}
let test_equal x y =
  match (x == y) with
      true -> :passed
    | false ->
        let msg = format_msg "Not equal:  ~w and ~w" x y in
        beam :erlang :error [msg] with _ -> :failed

-- formats a failure message:
let format_msg base x y =
  let m = beam :io_lib :format [base, [x, y]] with msg -> msg in
  beam :lists :flatten [m] with msg, is_chars msg -> msg
```


It's a bit of an open question right now as to whether we'll try to pull test assertions from EUnit's include file directly (likely the preferable way) or implement some matchers directly in Alpaca.

# Processes<a id="sec-7" name="sec-7"></a>

Process support in Alpaca is still pretty basic but the following are all supported:

-   spawn a function from the current module as a process with `spawn`
-   receive messages in a function with `receive`
-   send messages to process with `send`

A basic example will probably help:

```elm
let a_counting_function x =
  receive with
      "add" -> a_counting_function x + 1
    | "sub" -> a_counting_function x - 1

{- If a_counting_function/1 is exported from the module, the following
    will spawn a `pid string`, that is, a "process that can receive
    strings".  Note that this is not a valid top-level entry for a module,
    we just want a few simple examples.
  -}
let my_pid = spawn a_counting_function 0

-- send "add" to `my_pid`:
send "add" my_pid

-- type error, `my_pid` only knows how to receive strings:
send :add my_pid
```


The type inferencer looks at the entire call graph of the function being spawned to determine type of messages that the process is capable of receiving.  Any expression that contains a call to `receive` becomes a "receiver" that carries the type of messages handled so if we have something like `let x = receive with i, is_integer i -> i`, that entire expression is a receiver.  If a function contains it like this:

```elm
let f x =
  let x = receive with i, is_integer i -> i in
  i
```


then the entire function is considered a receiver too.

Mutually recursive functions can be spawned as well provided that **if** they're both receivers, the message receive types match:

```elm
let a () =
  receive with
      :b -> b ()
    | _ -> a ()

let b () =
  receive with
      "a" -> a ()
    | _ -> b ()

-- The above will fail compilation unless the following ADT is in scope:
type a_and_b = string | atom
```


As an aside, both the functions `a/1` and `b/1` above have the return type `rec`, meaning "infinitely recursive" since neither ever return a value.  This is a legitimate type in Alpaca.

# Exporting and Importing Functions<a id="sec-8" name="sec-8"></a>

There are a few handy shortcuts for exporting and importing functions to be aware of.  If you have different versions of a function (same name, different number of arguments) and you want to export them all, you can leave out the arity when exporting, e.g.

```elm
module example

-- this will export foo/1 and foo/2 for you:
export foo

let foo x = x

let foo x y = x + y
```


You can also import functions with or without arity, e.g. `import example.foo/1` for only the first `foo` in the example above or `import example.foo` for both versions.  Subsets of a module's functions can be imported in a list format as well, for example if we have a simple math helper module:

```elm
-- some simple math functions:
module math

export add, sub, mult

let add x y = x + y
let sub x y = x - y
let mult x y = x * y
```


We can then import two of the functions with a list:

```elm
-- imports and uses two of the math functions
module example

import math.[add, sub]

let f () = add 2 (sub 5 3)
```


When giving lists of functions to import you can include arity if you only want a specific version of a function.
