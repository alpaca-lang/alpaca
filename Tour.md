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
<li><a href="#sec-3-2-4">3.2.4. PIDs</a></li>
</ul>
</li>
</ul>
</li>
<li><a href="#sec-4">4. Functions</a>
<ul>
<li><a href="#sec-4-1">4.1. The Foreign Function Interface</a></li>
</ul>
</li>
<li><a href="#sec-5">5. User Defined Types:  ADTs</a></li>
<li><a href="#sec-6">6. Tests</a></li>
<li><a href="#sec-7">7. Processes</a></li>
</ul>
</div>
</div>

# Intro<a id="sec-1" name="sec-1"></a>

This document provides a tour of MLFE's current capabilities and limitations in a bit more depth for anyone looking to use it.

Some of ML Flavoured Erlang's goals:

-   A statically typed, strictly evaluated (eager, not lazy), and functional language for the Erlang platform.
-   Infer types as much as possible so we only need to be explicit where it matters.
-   A reasonably flexible approach to simple Algebraic Data Types (ADTs) .
-   Interoperate with existing Erlang code and libraries as safely as possible.

## Helpful Foundations<a id="sec-1-1" name="sec-1-1"></a>

If you're unfamiliar with Erlang itself, I'd highly recommend the excellent [Learn You Some Erlang for great good!](http://learnyousomeerlang.com/)  The sections on [the basic data types](http://learnyousomeerlang.com/starting-out-for-real) and on [modules](http://learnyousomeerlang.com/modules) will probably help a great deal to start understanding where MLFE fits and what it does.

Much of MLFE in its current state borrows (in an unstructured manner) aspects of a number of languages that descend from [ML](https://en.wikipedia.org/wiki/ML_(programming_language)) including:

-   [OCaml](https://ocaml.org/)
-   [Haskell](https://www.haskell.org/)
-   [Elm](http://elm-lang.org/)

While you probably don't need to know any of them in detail, some of the syntax in this document might make a bit more sense if you're familiar with one of the above (including ML).

## About This Document<a id="sec-1-2" name="sec-1-2"></a>

This document is exported from the Emacs org-mode doc `Tour.org` using `org-md-export-to-markdown`.  Corrections and suggestions welcome via PRs to the main [MLFE repository](https://github.com/j14159/mlfe).

# The Structure of a Program<a id="sec-2" name="sec-2"></a>

MLFE at present is really just a new way to write modules for an Erlang application.

## What Modules Include<a id="sec-2-1" name="sec-2-1"></a>

The set of top-level elements permitted in a module are the following:

-   a module declaration, e.g. `module my_module_name`.  This is required.
-   function exports.  These tell the compiler which functions should be publicly accessible to modules outside of the ones we write in MLFE.
-   type definitions.  These describe new types as ADTs.
-   test cases
-   comments, though these can go anywhere and are not restricted to the top level.
-   functions.  These can contain other functions and variables inside of them.

Here's a simple example of a module:

    module my_module
    
    // one function that takes a single argument will be publicly accessible:
    export double/1
    
    /* Our double function defines an "add" function inside of itself.
       Comments for now are C-style.
     */
    double x =
      let add a b = a + b in
      add x x
    
    test "doubling 2 is 4" = some_test_checker (double 2) 4
    
    // Basic ADT with type constructors:
    type even_or_odd = Even int | Odd int
    
    // A function from integers to our ADT:
    even_or_odd x =
      let rem = x % 2 in
      match rem with
          0 -> Even x
        | _ -> Odd x

Note that variables and function names follow the same format, beginning with a lower-case character.

# Included Data Types<a id="sec-3" name="sec-3"></a>

## The Basic Ones<a id="sec-3-1" name="sec-3-1"></a>

### Booleans<a id="sec-3-1-1" name="sec-3-1-1"></a>

Just `true` and `false`, not atoms as in Erlang although they're encoded as such after compilation.

### Numbers<a id="sec-3-1-2" name="sec-3-1-2"></a>

MLFE has integers and floats which can't mix with each other at all.  They have separate arithmetic instructions as in OCaml:

    1 + 2       // integer
    1.0 +. 2.0  // float
    1 +. 2      // type error, +. is only for floats
    1 +. 2.0    // type error, can't mix integers and floats

### Atoms<a id="sec-3-1-3" name="sec-3-1-3"></a>

Atoms in MLFE are just text prefixed with `:`, e.g. `:this_is_an_atom` and `soIsThis1`.

### Strings<a id="sec-3-1-4" name="sec-3-1-4"></a>

Strings in MLFE are all assumed UTF-8 and will be encoded as such:

    "This is a string"
    "so is 한국 and 日本"

These are compiled as binaries under the hood.  If you're looking for Erlang's basic string types, character lists can be constructed by prefixing a string with `c`, for example: 

    c"character list!"

### Binaries<a id="sec-3-1-5" name="sec-3-1-5"></a>

If you're not familiar with binaries, there's some [good coverage](http://learnyousomeerlang.com/starting-out-for-real) of them in [Learn You Some Erlang&#x2026;](http://learnyousomeerlang.com/)  At present in MLFE they're a little more verbose but also a little more obvious, e.g.

    <<"this text is assumed to be UTF-8">>
    <<"But we can also be explicit": type=utf8>>
    
    /* endian, sign, units and size all work, here's how we might encode
     * a 32-bit, big-endian, unsigned integer:
     */
    <<SomeInteger: type=int, size=8, unit=4, end=big, sign=false>>
    
    // of course you we just list off integers and floats too:
    <<1, 2, 3.14, 4, 5, 6.0>>

Endian settings can be `big`, `little`, or `native` as in Erlang.

## The Polymorphic Ones<a id="sec-3-2" name="sec-3-2"></a>

These types are all "parametrically polymorphic", or "generics" for those of us familiar with Java. This means that these types contain data of another type in a general manner so that we can have "a list of integers" and "a list of strings" without changing any of the code involving lists themselves.

### Tuples<a id="sec-3-2-1" name="sec-3-2-1"></a>

Tuples, like functions, have a specific arity (number of contained elements).  In MLFE the typing of tuples covers both their arity **and** the type of each element.  Let's introduce pattern matching here to illustrate their structure:

    third my_tuple =
      match my_tuple with
        (_, _, x) -> x
    
    third_string my_tuple =
      match my_tuple with
        (_, _, x), is_string x -> x
    
    third (1, 2, 3) // will return the integer 3
    
    /* The following will fail compilation with a type error because
     * third_string/1 only takes tuples that have strings as their
     * third element:
     */
    third_string (1, 2, 3)
    
    /* Both of the following will also fail compilation since the function
     * third/1 requires tuples with exactly 3 elements:
     */
    third (1, 2)
    third (1, 2, 3, 4)
    
    /* This function will also fail to compile because tuples of arity 2
     * those of arity 3 are fundamentally different types:
     */
    second_or_third my_tuple =
      match my_tuple with
          (_, _, x) -> x
        | (_, x) -> x

We can express the types of tuples with tuples themselves, for example `(int, string)` for tuples of integers and strings.

### Lists<a id="sec-3-2-2" name="sec-3-2-2"></a>

Lists compile directly to Erlang lists but of course they're type-checked. This means, for example, that we aren't able to mix integers and floats in the same list without creating an ADT that covers them both.  We can express "list of strings" with the type `list string`.

We can build lists up with the cons operator `::` or as literals:

    "end" :: "a" :: "cons'd" :: "list" :: "with the nil literal []" :: []
    ["or just put", "it", "in", "square brackets"]
    
    // type error:
    [:atom, "and a string"]

Let's revisit pattern matching here as well with both forms:

    length my_list =
      match my_list with
          [] -> 0
        | _ :: t -> 1 + (length t)
        
    is_length_3 my_list =
      match my_list with
          [_, _, _] -> true
        | _ -> false

### Maps<a id="sec-3-2-3" name="sec-3-2-3"></a>

Maps are type-checked as lists are but have separate types for their keys vs their values.  If we wanted a map with atom keys and string values, it could be expressed as the type `map atom string`.  Functionality is relatively limited still but we can construct literal maps, add single key-value pairs to maps, and pattern match on them.  

    #{:key => "value"}  // a literal
    
    /* This will cause a type error because the types of the keys
     * don't match:
     */
    #{:key1 => "value 1", "key 2" => "value 2"}

### PIDs<a id="sec-3-2-4" name="sec-3-2-4"></a>

Process identifiers (references to processes to which we can send messages) are typed with the kind of messages they are able to receive.  The type of process that only knows how to receive strings can be expressed as `pid string`.  We'll cover processes and PIDs in a bit more detail later but if you're unfamiliar with them from Erlang, [The Hitchhiker's Guide to Concurrency](http://learnyousomeerlang.com/the-hitchhikers-guide-to-concurrency) from Learn You Some Erlang is a great place to start.

# Functions<a id="sec-4" name="sec-4"></a>

Inside of a function we can define both immutable variables and new functions:

    f x =
      let double y = y + y in      // this is a single argument function
      let doubled_x = double x in  // a variable named "double_x"
      doubled_x + x                // the expression returned as a result

As MLFE is an expression-oriented language, there are no return statements.  Just as in Erlang, the final expression in a function is the value returned to the caller.

While functions with no arguments aren't supported ("nullary" or arity of zero) we can use the unit term `()` if we don't need or want to pass anything specific.  Let's introduce the basic foreign-function interface here to call an Erlang printing method:

    print_hello () =
      call_erlang :io :format ["Hello~n", []] with _ -> ()

## The Foreign Function Interface<a id="sec-4-1" name="sec-4-1"></a>

The FFI is how we call any non-MLFE code.  Since the compiler can't type-check other languages, we use a set of pattern match clauses to figure out what the actual type is that we're returning.  Here we're using a simple guard function so that we know the FFI expression is returning characters (an Erlang string):

    call_erlang :io_lib :format ["This will contain the integer 3:  ~w", [3]] with
      cs, is_chars cs -> cs

The FFI `call_erlang` expects the external module and function as atoms and then a list of arguments to send.  The arguments sent are **not** type checked but the return value in the pattern matching clauses **is** checked.

# User Defined Types:  ADTs<a id="sec-5" name="sec-5"></a>

While there isn't yet a way to specify the type of a variable or a function (it's coming soon), we can specify new types as ADTs and they will also be inferred correctly.  Here's a simple polymorphic option type:

    type opt 'a = Some 'a | None
    
    //here's a map "get value by key" function that uses the new `opt` type:
    map_get key the_map =
      match the_map with
          #{key => value} -> Some value
        | _ -> None

You can use the basic MLFE types as well, here's a type that describes parsed JSON data based on how the [JSX](https://github.com/talentdeficit/jsx) library represents it:

    type json = int | float | string | bool
              | list json
              | list (string, json)

If the above type is in scope (in the module, or imported), the following function's type will be inferred as one from `json` to `atom`:

    f x =
      match x with
          i, is_integer i -> :integer
        | f, is_float f -> :float

If the inferencer has more than one ADT unifying integers and floats in scope, it will choose the one that occurs first.

# Tests<a id="sec-6" name="sec-6"></a>

Support for tests inside source files is currently at its most basic with the goal of keeping unit tests alongside the functions they're testing directly rather than in a separate file.  

Tests:

-   can occur anywhere within a module
-   are only compiled and exported if the compiler is told to run in test generation mode (the atom `test` given in its options)
-   are run by [EUnit](http://erlang.org/doc/apps/eunit/chapter.html)
-   fail if an error/exception is thrown in the test's expression

Here's a simple example:

    add x y = x + y
    
    test "add 2 2 should result in 4" =
      add 2 2

While the above test is type checked and will happily be compiled, we lack assertions to actually validate the test expression.  They can be built relatively simply for now, here's an example from one of the test files, `basic_module_with_tests.mlfe`:

    // formats a failure message:
    format_msg base x y =
      let m = call_erlang :io_lib :format [base, [x, y]] with msg -> msg in
      call_erlang :lists :flatten [m] with msg, is_chars msg -> msg
    
    /* Test the equality of two terms, throwing an exception if they're
     * not equal.  The two terms will need to be the same type for any
     * call to this to succeed:
     */
    test_equal x y =
      match (x == y) with
          true -> :passed
        | false ->
            let msg = format_msg "Not equal:  ~w and ~w" x y in
            call_erlang :erlang :error [msg] with _ -> :failed

It's a bit of an open question right now as to whether we'll try to pull test assertions from EUnit's include file directly (likely the preferable way) or implement some matchers directly in MLFE.

# Processes<a id="sec-7" name="sec-7"></a>

Process support in MLFE is still pretty basic but the following are all supported:

-   spawn a function from the current module as a process with `spawn`
-   receive messages in a function with `receive`
-   send messages to process with `send`

A basic example will probable help:

    a_counting_function x =
      receive with
          "add" -> a_counting_function x + 1
        | "sub" -> a_counting_function x - 1 
    
    /* If a_counting_function/1 is exported from the module, the following
     * will spawn a `pid string`, that is, a "process that can receive 
     * strings".  Note that this is not a valid top-level entry for a module,
     * we just want a few simple examples.
     */
    my_pid = spawn a_counting_function [0]
    
    // send "add" to `my_pid`:
    send "add" my_pid
    
    // type error, `my_pid` only knows how to receive strings:
    send :add my_pid

The type inferencer looks at the entire call graph of the function being spawned to determine type of messages that the process is capable of receiving.  Any expression that contains a call to `receive` becomes a "receiver" that carries the type of messages handled so if we have something like `let x = receive with i, is_integer i -> i`, that entire expression is a receiver.  If a function contains it like this:

    f x = 
      let x = receive with i, is_integer i -> i in
      i

then the entire function is considered a receiver too.

Mutually recursive functions can be spawned as well provided that **if** they're both receivers, the message receive types match:

    a () =
      receive with
          :b -> b ()
        | _ -> a ()
    
    b () =
      receive with
          "a" -> a ()
        | _ -> b ()
    
    // The above will fail compilation unless the following ADT is in scope:
    type a_and_b = string | atom

As an aside, both the functions `a/1` and `b/1` above have the return type `rec`, meaning "infinitely recursive" since neither ever return a value.  This is a legitimate type in MLFE.
