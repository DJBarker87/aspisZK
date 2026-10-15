# PublicBase under ring-hom mapping

This focused Lean result proves that mapping an `R0P.Public K` through a ring homomorphism places each field-valued coordinate in the homomorphism's field range. The theorem covers the nine conjuncts of `R0P.PublicBase`, including mapped recipient and withdrawal-amount options. It is structural representation plumbing; it does not prove source-byte correspondence or acceptance.

Attempt `a` failed on option-value proof plumbing and is retained; its failed theorem emitted a `sorryAx` report. Attempt `b` compiled successfully with the same statement. The successful NUC run used Lean 4.32.0 under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`; elapsed time was 1.43 s, maximum RSS 3,328,932 KiB, swap 0. Its output reports `[propext]` for `mapPublic_base`.

The `R0P.CoreExt` object was supplied through the pinned NUC workspace's symlink to the frozen `aspis-fs-generic-20261006/objects/R0P/CoreExt.olean`. The source is retained here from the repository's v8 R0 semantic proof tree. This records the available source and cache object; it does not claim a source/object build relation for that frozen dependency.
