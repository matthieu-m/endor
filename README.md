A compiler toolkit

#   Status

Experimental.


#   Goals

Provide the missing bricks upon which to bring efficient parallel compilers.

There are many parsing libraries, there are typing algorithms, but very few libraries address the lower-level bricks needed to build up a compiler:

-   How do you intern strings?
-   How do you store an AST, HIR, MIR, CFG?
-   How do you schedule the compilation of items with complex inter-dependencies?
-   How do you incrementally compile, only recalculating the minimum needed compared to the last run?

The goal of endor is to offer an answer to these oft-neglected questions.


#   Non-Goals

Endor aims to be neutral towards the exact datamodel and algorithms used.


#   Alternatives

This author is only really aware of the [`salsa`](https://github.com/salsa-rs/salsa) framework in the same space.


#   Why endor?

This author got a chuckle from the gimli crate, a crate used to parse DWARF information, and decided that Middle Earth would thus be an appropriate foundation to build upon.
