# QueryAccumulator focused Lean result

`R1QueryAccumulator` states a symbolic accumulator recurrence. The fixed-size
`run22` wrapper repeats `Fin 22` inputs by index modulo 22; its closed forms
show next index 22, power `rho ^ 22`, 64 challenge-weight sums, and the
embedded right-hand-side sum. This is a theorem about the declared recurrence,
not a Rust refinement or protocol claim.

Final source: `docs/research/100bit-spend-path-20261013/lean/QueryAccumulator.lean`
SHA-256 `0226833656670caa39e7bc9c687f5bae5c114a6c522431a8d5fdedb46ae949b6`.
The focused target was `R1QueryAccumulator` in the pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`, using
`compile-one.sh R1QueryAccumulator e`. Attempt e exited 0 in 1.15 s, peak RSS
2,081,996 KiB, swap 0, with `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, and Lean threshold 5000 MB. The five original recurrence
theorems and five `run22` theorems each print axioms
`[propext, Classical.choice, Quot.sound]`. The compiled object is
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1QueryAccumulator.olean`.

Attempts b–d are retained with exact source hashes, logs, and timing receipts.
They exited 1 on proof plumbing: b exposed unreduced `run22` projections and a
malformed calc step; c/d corrected the projections but still had a calc parser
error in the right-hand-side goal. Attempt e uses explicit calc chains from
`run_closed_forms`; it is the green result. No attempt exceeded the same cap.

The workspace source revision was `3638d7546f6e03a1afb0eaabdb1cff38d1631e84`;
the dirty Lean source hash above identifies the exact compiled file. Attempt a
is also retained as the earlier green compile of the generic recurrence before
adding the fixed-22 wrapper.
