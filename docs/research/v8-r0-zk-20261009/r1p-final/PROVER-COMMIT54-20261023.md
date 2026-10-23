# Part 54: owned simulator encoder

Target not yet established. Branch `codex/cx-prover-commit54-20261023`.
Allocated attempts J10600–J10699 only. No shipped source is changed.

## Endpoint before/after

Verbatim endpoint modules are retained in `endpoint/before.lean.txt` and
`endpoint/after.lean.txt` under the part-54 evidence directory. Both currently
retain the deployed RustProverRefinement premise. No payload equality is claimed.

## Stage 1: explicit encoder owner

The owner uses an explicit finite recursive strided collector and a finite-height
evaluator. Four channel vectors are built without iterator adapters. Extraction,
source binding, native equivalence and model induction are separate obligations.

Charon/Aeneas succeed (1.458/0.476 s, 210996/71280 KiB, zero swap).
J10603 checks the exact extracted declarations after byte-identical arithmetic
rebinding. J10608 proves the complete strided collector output, including every
read index, output ordering, finite termination, and release wrapping bounds.
It exits 0, 2.53 s, 4118444 KiB, zero swap; all four printed axioms are standard.

J10600 exposes missing Lean 4.32 core companion artifacts. J10601 is refused
without a compiler invocation. The cache completion adds read-only links, and
the dependency fingerprint now records the actual split core artifacts. J10602
exposes two omitted conversion imports, repaired by reusing byte-identical
Samples49 declarations. J10604–07 are rejected collector proof drafts; their
full diagnostics are retained. No cap or heartbeat limit is raised. Receipts
pin source revision and exact source/dependency hashes. The accepted source
has no proof holes. No shared object is overwritten.
