Fzip
====

Description
-----------

This project implements the language that is described in the last
part of Benoît Montagu's PhD thesis. It is an extension of System F
with subtyping, singleton kinds and open existential types. This
implementation is was not designed to be efficient, and, indeed, it is
not efficient (most algorithms are quadratic in the size of terms).

The representation of binders is the one from Sato & Pollack. For more
details, see the following articles:

* [A Canonical Locally Named Representation of Binding](http://homepages.inf.ed.ac.uk/rpollack/export/PollackSatoRicciottiJAR.pdf)
* [External and Internal Syntax of the Lambda-calculus](http://homepages.inf.ed.ac.uk/rpollack/export/SatoPollack09.pdf)

To get an overview of the syntax, see the examples in the examples
subdirectory. The files can use UTF-8 symbols: for instance, 'λ' can be
used instead of 'fun', or '→' instead of '->'. The user is invited to
read the file lexer.ml to get more info.

Requirements:
-------------

* make
* Objective Caml >= 3.12
* ocamlfind
* ulex
* menhir
* OUnit (for running tests)

How to build:
-------------

To build, type in a terminal:

`make`

To build a native version, type:

`make native`

How to run tests:
-----------------

To run tests, type:

`make test`

or to run them in native mode:

`make test.native`
