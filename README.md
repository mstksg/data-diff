# data-diff

Three priorities:

1.  Generalize the idea of "diffing" to different data structures in a
    meaningful way
2.  Be able to inspect and manipulate patches, and to apply manipulated patches
    to update data structures, for three-way merging
3.  Automatically derive diffing capabilities for data types using GHC
    Generics.

## Comparisons

*   *[gdiff][]* doesn't integrate with GHC Generics; the "g" stands for
    lowercase "generic" (as in, polymorphic) and not GHC Generics.  Its
    interface/API is also a bit dated, and its auto-deriving packages no longer
    build with current TH API.

*   *[tree-diff][]* doesn't have patching capabilities (update based on diff)

*   *[Diff][]* is only for diffing linear sequences (not data structures in
    general).  This library actually uses *Diff* internally to implement
    diffing for sequences.

[gdiff]: http://hackage.haskell.org/package/gdiff
[tree-diff]: http://hackage.haskell.org/package/tree-diff
[Diff]: http://hackage.haskell.org/package/Diff
