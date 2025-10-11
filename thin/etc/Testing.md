#   Miri

The test-suite runs under Miri, but _only_ using the Tree Borrows model.

```sh
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test --all-features
```

For our purpose, the main difference between the Stacked Borrows and the Tree Borrows model is that Tree Borrows allows
accessing a memory block from a sub-part of the memory block while Stacked Borrows does not.

This comes up due to the use of the standard (if unstable) `ThinBox` to const-allocate unsized ZSTs. The API of
`ThinBox` only allows recovering a reference to `T`, and therefore under Stacked Borrows only allows access to the `T`
portion of the memory block, and not to the pointee metadata stored prior to `T`.

The alternatives are thus:

-   Shunning the optimization. Pure ZSTs would still be optimized, but unsized ZSTs would allocate.
-   Performing the const allocation directly. Unfortunately this means using intrinsics, which are perma-unstable, and
    finicky.
-   Using `ThinBox`, and accepting that only Tree Borrows will vet the code.

For now, the latter option was picked.
