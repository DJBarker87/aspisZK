# Raw two-fold pairing focused Lean result

`R1RawPairing` proves linearity of the radix-four dual fold and dot product,
then shows that two nested dual folds of the functional weights paired with
`f` equal the sum of the seven embedded raw-row pairings with coefficients
`kappa^k.val`. This is an algebraic identity; it does not establish equality
with an optimized Rust pairing implementation.

Final source:
`docs/research/100bit-spend-path-20261013/lean/RawPairing.lean`, SHA-256
`57c22ff34f590669e64c5ae41f1235ff003f014f7f24823f544705f72f5186de`.
Focused target `R1RawPairing` compiled in pinned workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with
`compile-one.sh R1RawPairing c`. Attempt c exited 0 in 1.22 s, peak RSS
2,227,032 KiB, swap 0, with `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, and Lean threshold 5000 MB. All four printed theorem axiom
lists are `[propext, Classical.choice, Quot.sound]`. Object:
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1RawPairing.olean`.

Attempts a–b are retained with source hashes, logs, and timing receipts; they
exited 1 on proof plumbing. Attempt c is the green result. Workspace source
revision: `3638d7546f6e03a1afb0eaabdb1cff38d1631e84`; the final dirty-source
hash identifies the exact compiled file.
