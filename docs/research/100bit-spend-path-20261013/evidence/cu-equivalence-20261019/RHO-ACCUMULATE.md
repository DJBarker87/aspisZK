# Whole source accumulation equivalence (2026-10-20)

`CuSavingsRhoAccumulate.source_equivalence` now compares the complete old/new
`accumulate_with_node` outcomes, observing pending coefficients through the
actual source materializer. It includes errors and divergence of basis,
coefficient, RHS and power computations, and counter overflow. There is no
child-call success premise or assumed kernel equivalence.

`source_preserves` derives the next raw bounds, canonical power, incremented
counters and weight-length relation from a successful whole source call and
the pre-state invariant. This supplies the induction step needed by the actual
query loops. Starting allocation/resume invariants remain open.

Both actual function bodies come from the exact candidate/parent, with only
inverse-checked factoring at the already proved basis and coefficient source
blocks. The entire emitted caller bodies are unchanged. Identical carriers are
aliased explicitly. Unchanged RHS functions are arbitrary common computations,
with no propositional success/canonicality/equivalence assumption. Both source
basis calls, coefficient loops, power multiplication and non-prover trace bind
their checked source implementations.

The successful focused result is `rho-accumulate-proof-e`: exit 0, 2.407 seconds,
peak RSS 2,396,760 KiB, zero process swaps. Both theorems print only `propext`,
`Classical.choice`, `Quot.sound`. Full command, revision, features, source/object
and cache pins, RSS/swap, and audits are in `RHO-ACCUMULATE.json` and the receipts.

Reproduce the source/receipt audit with `check-rho-accumulate.py`. It checks
inverse factoring and raw function preservation without rerunning Lean.
The final candidate-level theorem is still open: initialization and reserve
resources, resumed-weight canonicality, query/stage loops, and transaction
checkpoint/hash-order/settlement contexts must still be composed.
