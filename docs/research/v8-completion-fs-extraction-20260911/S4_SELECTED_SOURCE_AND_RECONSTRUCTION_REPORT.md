# S4 selected-source and reconstruction continuation

Base: `6279cccf41ffc0c67008918992d3a1cf6e45f6f3`.

This continuation consumes S2's positional root-label result and S3's
unprojected verifier suffix.  It adds checked algebraic consumers and a
dynamic-prelude composition wrapper.  It does **not** establish selected-source
fresh-output production, actual ordinary-event inclusion, replay collection,
checked-payment extraction, Fiat--Shamir soundness, or a global security bound.

## Checked results

| Result | Meaning | Source boundary retained |
|---|---|---|
| `FSV8S4VerifierOnlySuffix.selectedSuffix` | The OOD-to-gamma selected suffix fixes both prover-work hooks to `done ()`; OOD answers remain body reads and cached/adversary prehistory is unchanged. | It is a fixed-context suffix, not the actual `semantic()` prelude. |
| `FSV8S4DynamicPrelude.withPrelude_run` | A source-provided semantic prelude and dependent suffix run in the same oracle; rejection retains the exact oracle state. | The actual selected semantic producer is not yet represented as this `Script`. |
| `FSV8S4CompactEvaluationBridge.actual_compact_evaluation` | The concrete `ringArithmetic.evaluate7` is `Polynomial.ofFn 7` evaluation of the actual compact vector. | No Rust evaluator refinement or wire-to-`sent` bridge. |
| `FSV8S4CompactEvaluationBridge.classify_collision` | For a supplied prechallenge candidate list, a collision is exact polynomial equality or membership in a finite root target of size at most `6 * length`. | The selected source has not produced that list, its fixing time, or actual-event inclusion. |
| `FSV8S4RecoveredHighMatrix.recovered_high_matrix_constructs_family_member` | 29 gamma rows times four alpha finals reconstruct a tuple in the literal fixed `RecoveredHigh` family. | All 116 usable continuations, replay law and bounded collection are still hypotheses/open producers. |
| `FSV8S4RecoveredHighMatrix.recovered_high_matrix_has_early_projection` | The computed tuple inherits the literal event's early-C1 projection membership. | This is neither an enumerator nor a payment validator. |

The 29x4 construction retains the actual adaptive final vectors, same-quotient
high-support uniqueness and the fixed-family cardinality-one premise.  It does
not filter candidates by a noncomputable event predicate.

## Focused evidence

The S4 archive manifest and source-pin check both passed.  The latter matched
30 selected blob identities against this exact base; it is not a source
refinement theorem.

`python3 scripts/verify.py` from the S4 pack passed 76/76 finite/reference
tests.  `python3 scripts/full_matrix.py` reconstructed 29,696 coefficients
from 116 synthetic final vectors, checked 59,392 nodal equalities and 29 image
conditions.  It is reference arithmetic only, not an actual Aspis replay.

Pinned Lean 4.32.0 on the Tailscale NUC was invoked through a separate
`systemd-run --user --scope` for each leaf with `MemoryHigh=7500M`,
`MemoryMax=8G` and `MemorySwapMax=0`:

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8S4VerifierOnlySuffix` | 0 | 2.70 s | 6,796,024 KiB | 0 | standard only |
| `FSV8S4DynamicPrelude` | 0 | 3.01 s | 6,805,172 KiB | 0 | standard only |
| `FSV8S4CompactEvaluationBridge` | 0 | 1.87 s | 3,381,116 KiB | 0 | standard only |
| `FSV8S4MatrixReconstruction` | 0 | 3.12 s | 6,735,324 KiB | 0 | standard only |
| `FSV8S4RecoveredHighMatrix` | 0 | 2.89 s | 6,735,708 KiB | 0 | standard only |

“Standard only” means `propext`, `Classical.choice`, and `Quot.sound`; the
printed promoted declarations contained neither `sorryAx` nor a custom axiom.
This is focused compilation and axiom hygiene, not a clean dependency rebuild
or fresh external kernel replay.

## Exact selected-source blocker

The selected host verifier source supports the no-work OOD observation: its
two OOD rows are already parser-validated body data and are absorbed without
an intervening prover-work callback.  The formal `Configuration`, however,
still takes `z`, `initialDigest`, `adversaryFuel`, and the full source-history
facts as caller data.  The selected `semantic()` transcript computes `z` and
its digest dynamically in the same oracle.  There is no existing Lean source
constructor/refinement that supplies `FSV8S4DynamicPrelude`'s `prelude` from a
successful canonical selected verifier run.

Likewise, no producer currently proves on the same root that every consumed
ordinary-alpha output is a first use of its routed coordinate with residual
capacity available.  A static 185/186 suffix arithmetic table cannot create
that chronological fact; cached outputs must remain cached and a mere local
table miss is insufficient.  Therefore the desired source ordinary-event
inclusion cannot be stated without assuming precisely the missing producer.

## Next decisive work

Formalise the actual `performance_verifier.rs::semantic` prelude as a same-body,
same-oracle `Script`, then factor the actual compiled selected verifier root at
the pre-alpha cut.  That one producer must return the dynamic context, complete
mixed history, selected marker grammar, residual capacity and every consumed
fresh output occurrence.  Only then can the compact finite-root consumer be
applied to an actual ordinary collision.  In parallel, a separate permitted
replay/restoration theorem must produce the 29x4 usable-node family before the
reconstruction endpoint can be connected to payment validation.

## Claim supported by this continuation

None beyond the scoped algebraic and execution-composition statements listed
above.  In particular, this continuation supports no global soundness,
Fiat--Shamir, zero-knowledge, payment-extraction, production, CU, or security-bit
claim.
