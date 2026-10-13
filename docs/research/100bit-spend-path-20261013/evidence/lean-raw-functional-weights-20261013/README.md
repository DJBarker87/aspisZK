# Raw functional weights focused Lean result

`R1RawFunctionalWeights` defines the `E`-linear `rowMap` for an embedded raw
coefficient row, six maps from rows 1–6, and the base map from row 0. It proves
that `FunctionalWeights.weights` evaluated at coordinate `i` equals
`Σ k : Fin 7, kappa^k.val * iota (raw k i)`. It also identifies `rowMap` with
the embedded coefficient dot product. These are algebraic identities only;
they do not identify `raw` with Rust constructors or semantic functionals.

Final source:
`docs/research/100bit-spend-path-20261013/lean/RawFunctionalWeights.lean`,
SHA-256 `9fa7cf8d71eac207612477bbce249d801fde05b9a11f7cd9862771e1059f583b`.
Focused target `R1RawFunctionalWeights` compiled in pinned workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with
`compile-one.sh R1RawFunctionalWeights g`. Attempt g exited 0 in 1.18 s, peak
RSS 2,225,600 KiB, swap 0, under `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, and Lean threshold 5000 MB. The three exported theorem
axiom lists are `[propext, Classical.choice, Quot.sound]`. Object:
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1RawFunctionalWeights.olean`.

Attempts a–f are retained with their exact source hashes, logs, and timing
receipts; those attempts exited 1 during proof plumbing. Attempt g is the green
result. The workspace source revision was
`3638d7546f6e03a1afb0eaabdb1cff38d1631e84`; the final dirty-source hash above
identifies the compiled source.
