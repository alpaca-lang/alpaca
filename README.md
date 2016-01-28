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
