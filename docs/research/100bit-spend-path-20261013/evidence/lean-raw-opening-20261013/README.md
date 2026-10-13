# Raw opening interface focused Lean result

`R1RawOpening` packages the existing matching-support data with arbitrary
seven-row coefficients. `claims_iff_raw` expands the two linear-functional
claims to their coefficient sums, `accepted_pairing_iff_raw` replaces the
weighted final pairing by the seven embedded-row pairings, and
`large_matching_implies_raw_claims` applies the existing deterministic
matching theorem. These are algebraic interfaces only; they do not identify
the raw rows with Rust constructors or establish a semantic/security gate.

Final source:
`docs/research/100bit-spend-path-20261013/lean/RawOpening.lean`, SHA-256
`9dbb707f5f96af34979950cab3471392e8e67b9a3bb1ac31705bd55f56ec63d0`.
Focused target `R1RawOpening` compiled in pinned workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with
`compile-one.sh R1RawOpening d`. Attempt d exited 0 in 1.76 s, peak RSS
3,156,716 KiB, swap 0, under `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, and Lean threshold 5000 MB. All three exported theorem
axiom lists are `[propext, Classical.choice, Quot.sound]`. Object:
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1RawOpening.olean`.

Attempts a–c are retained with source hashes, logs, and timing receipts; they
exited 1 on proof plumbing. Attempt d is the green result. Workspace source
revision: `3638d7546f6e03a1afb0eaabdb1cff38d1631e84`; the final dirty-source
hash identifies the exact compiled source.
