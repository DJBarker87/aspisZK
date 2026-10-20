# R4 transport continuation

Base 54054b905; branch codex/cx-r4-transport2-20261021. Focused cached-object
proofs, not a coherent frozen release replay. No endpoint premise is removed.

## Stage 1: wide reference and source steps

The exact optimized long-division limb and carry limb pass Kani under,
respectively, remainder < P and canonical digit < P, addend <= 257.
The complete shipped add_small_base_p passes against an indexed reference,
including every output digit and the final carry. Library traversal checks
show the eight reverse mutable visits and eight from_fn callback positions.
All checks retain unwinding assertions and use the capped host scope.

R4Transport2WideReference composes the *actual extracted* qm31_div_pass eight
times, preserving the entire quotient array, and proves its low digits and
remaining positional value equal the byte-rank Lean model. It has no
pass-success hypothesis; byte-array decoding is an explicit input equality.
All three top theorem audits are standard, zero swaps. Attempts 1 and 2
failed on do-pattern reduction; attempt 3 changes the wrapper to projections
and passes. No unchanged failed source was retried.

The syntactic step checker identifies the identical divider in both optimized
and indexed reference loops. This is not a kernel theorem about Rust's
from_fn/iter_mut library implementations. A whole-helper compiler/extraction
join, including the final quotient-array debug assertions and the connection
of the indexed add reference to its existing extraction, remains explicit.

## Stage 2: scanner step, invariant and selected state

All 23 fixed-length source-step partitions pass (37.286 s total, peak
591908 KiB, zero swap). Each starts with arbitrary stored words, arbitrary
candidate and draws <= 64. The exact source step is checked against indexed
membership, guard, length/draw updates and every unchanged array cell.
This replaces the earlier whole-block timeout; no old failed job was rerun.

R4Transport2ScanComposition proves a complete single-step relation lifts to
an arbitrary-length scan, preserves the bounded/distinct invariant, and
proves the materialized-pair driver equals Q22.scanOut under its reached
8-word budget. The eight-pair specialization has no assumption that advances
are distinct or that the returned state is advance7. Four new theorem audits
are standard, zero swap. The driver theorem includes the stop-before-word
behavior and the extra block after success on the previous eighth word.

Kani and Lean are separate proof engines: scan_loop_refines states the exact
relation their embedding must supply. The source splice checker and all 23
Kani partitions are evidence for the source step, not a newly accepted Lean
axiom for generated IntoIter methods. The existing extraction's external
iterator implementation boundary is still not a kernel-checked theorem.
