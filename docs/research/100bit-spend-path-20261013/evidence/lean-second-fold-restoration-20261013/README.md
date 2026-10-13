# SecondFoldRestoration focused Lean result

`R1SecondFoldRestoration` is a focused encoder-restoration module. Its stated
result is conditional on channel agreement on parent support and identifies
the original word with the exact log-18 encoder of the joined four messages
on complete quartets. It makes no runtime, source-correspondence, transcript,
or security claim.

The final source is
`docs/research/100bit-spend-path-20261013/lean/SecondFoldRestoration.lean`,
SHA-256 `fdf4d5a8b349f11e46185c96ceab4623fe0fd5b74ec875ca12378146c3709127`.
It compiled as target `R1SecondFoldRestoration` in the pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with:

```sh
bash compile-one.sh R1SecondFoldRestoration m
```

The runner invoked the focused `run2.py` target with `MemoryHigh=4G`,
`MemoryMax=6G`, `MemorySwapMax=0`, and a 5000 MB Lean threshold. Attempt m
exited 0 in 2.53 s, peak RSS 2,776,208 KiB, swap 0. The printed axioms for
`x0_ne_zero`, `x1_ne_zero`, `x2_ne_zero`, `inverse_products`, both channel
identities, `lane_join`, `fold_join`, and `secondFoldRestoration` were all
`[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`.

The NUC compile workspace was at source revision
`2df5bf1a6f296a09cff71a886185112b66f0235a`; the target source itself was the
hash above. The successful object is
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1SecondFoldRestoration.olean`.

All attempts a–m are retained in this directory, including source hashes,
receipts, logs, and timing/resource records. Attempts a–l exited nonzero while
proof plumbing was being corrected; attempt b was a pre-Lean reservation
rejection. No attempt raised the 4G/6G/zero-swap cap. The final attempt m is
the only green result.
