# NaturalEmbedding focused Lean result

`R1NaturalEmbedding` proves that a ring hom commutes with the repeated
`2x²-1` basis and that every hom from the prime field agrees with the
canonical `ZMod P` algebra map. It then rewrites the existing log-16
`secondEncoder` at the parent of an arbitrary log-18 query as the sum of the
embedded K-valued natural basis. This is algebraic embedding plumbing only.

The final source is
`docs/research/100bit-spend-path-20261013/lean/NaturalEmbedding.lean`,
SHA-256 `c82cb783bd33e31d71e3fd2474aca6aba563ed38f6136de7cf67054e685229fe`.
It compiled as target `R1NaturalEmbedding` in the pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with:

```sh
bash compile-one.sh R1NaturalEmbedding b
```

Attempt b exited 0 in 1.24 s, peak RSS 2,747,564 KiB, swap 0, under
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, with a 5000 MB Lean
threshold. The four printed theorem axiom lists were each
`[propext, Classical.choice, Quot.sound]`. The compiled object is
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1NaturalEmbedding.olean`.

The workspace base revision was `3638d7546f6e03a1afb0eaabdb1cff38d1631e84`;
the target source hash above identifies the dirty file compiled. Failed
attempt a and successful attempt b are retained with source hashes, logs,
receipts, and timing/resource records.
