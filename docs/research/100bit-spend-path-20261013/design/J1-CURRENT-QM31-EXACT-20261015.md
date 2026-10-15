# Current extracted arithmetic to exact QM31

The [current arithmetic checkpoint](J1-CURRENT-QM31-ARITHMETIC-20261015.md)
now has a checked interpretation in the same `QM31Exact` field used by the
security model. For canonical inputs, current extracted QM31 addition and
multiplication return canonical values whose decoding equals mathematical
addition and multiplication. A separate checked lemma proves that two
canonical current values decode equally if and only if their records are equal.
This is not yet a theorem about the Rust verifier's acceptance or comparisons.

The bridge reuses `QM31WordFormulas`, `QM31WordResidues`,
`QuadraticTowerOperations`, `QM31WordTower` and `ExactTowerBase` unchanged.
Together with the previously reused `RawReducerNat`, six historical modules
are used byte-for-byte. The two adapter files introduce only coordinate decoding
and compose the existing results; they introduce no field or security premises.
Canonical-input assumptions remain explicit and must be supplied by the caller.

The [root review](../evidence/current-qm31-exact-lead-review-20261015.json)
covers seven new bridge/dependency targets and the equality follow-up. There
are 27 axiom reports: 26 use only standard Lean axioms and one is axiom-free.
All eight targets passed on Lean 4.31.0 with cached libraries; the maximum
sampled aggregate process RSS was 3,083,552 KiB, and all process swap counts
were zero. The
[bridge bundle](../evidence/current-qm31-exact-20261015/README.md) and
[equality bundle](../evidence/current-qm31-equality-20261015/README.md)
retain exact sources, commands, receipts and objects. One failed exact-adapter
attempt remains separate; direct definitional conversion replaced a failed
simplifier step without changing its statement.

One timing discrepancy is retained rather than reconciled without evidence:
`current-word-tower-a` recorded 16.813 seconds via the runner's monotonic clock
and 767.63 seconds via `/usr/bin/time`. The cause is unestablished. The proof
exited successfully; these numbers should not be used as a performance claim.

## Source inventory correction

The earlier arithmetic bundle's read-only inventory described the semantic
boundary fold as adding the other 27 coefficients. That description is wrong.
At current `r1_semantic.rs:86`, the fold is seeded with coefficient zero and
iterates **all 28** coefficients. It computes `p(0) + p(1)`, so coefficient
zero occurs twice. The production source is unchanged; future correspondence
proofs must preserve this exact behavior. The frozen old inventory is retained
with this explicit correction.

## Remaining work

These contracts cover ordinary field operations, not the optimized
`PreparedQm31Multiplier` used by the mask and terminal code. Successful strict
parsing must still be connected to the exact values used by those callers.
The semantic boundary/Horner loops, mask schedule, terminal evaluator,
transcript/challenge correspondence and actual acceptance-to-terminal
conditions remain open. The commitment compiler, efficient extraction,
privacy and complete admitted-runtime release gates remain open as well.

The target remains a transparent spend with 100-bit per-attempt soundness,
without grinding credit, using at most two verification/settlement transactions.
This arithmetic bridge does not by itself establish that target.
