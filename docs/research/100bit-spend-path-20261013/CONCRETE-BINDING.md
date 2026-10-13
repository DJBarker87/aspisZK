# Concrete two-fold algebraic binding

2026-10-13. `lean/ConcreteBinding.lean` now proves the deterministic binding
step that was previously a design obligation. It does not prove the complete
private-spend or Fiat--Shamir claim.

The theorem works over a finite field with an algebra embedding of M31. Its
initial and final encoders are the repository's actual 1024- and
256-coefficient encoders on stored domains. The added 64-coefficient encoder
evaluates on the concrete stored log-16 nodes. No abstract decoder or
inverse-correctness assumption is introduced.

Given fixed initial words W and intermediate word V, a nonzero gamma, two
fold challenges and the final 64-element message, `TwoFoldExtraction` proves:

- 9558 matching first-layer positions touch at least 2390 distinct parents.
- Repetition into the existing 256-coefficient code transfers its unchanged
  matched-response cap to the second fold. The averaging/overlap argument
  proves that all matching component messages descend to 64 coefficients.
- Concrete inverse identities restore V on every quartet over those parents,
  including all original matching positions.
- First-fold matching restores the batched initial word on at least 38232
  positions. Existing width-29 matching yields a tuple in the literal
  `Lambda W`, whose size is proved at most 100.
- The announced final message is the twofold coefficient fold of that
  tuple's gamma-batch.

`ConcreteBinding.binding` passes that same tuple through both round-polynomial
comparisons. `FunctionalWeights` derives the coefficient weights of the
inactive functional plus the six kappa-weighted functionals. The direct
gamma/kappa comparison then recovers every one of the six claims for each
of the 29 lanes, together with the inactive functional claim on the batch.
No unique-candidate premise is used.

The module also proves these explicit combined bad-set cardinalities:

| Challenge row | Cardinality cap | Construction |
|---|---:|---|
| gamma | 336869026622539 | existing width-29 unmatched-response set + 16800 functional roots |
| kappa | 600 | six-degree discrepancy union over the literal list |
| alpha0 | 9396508281846 | existing four-channel unmatched-response set + 600 round roots |
| alpha1 | 9396508281846 | repeated-lift unmatched-response set + 600 round roots |

These are counts, not probability or bit-security statements. Gamma is
required to be nonzero; the source uses a nonzero sampler, whose connection
to the model must be accounted for in the sampling/Fiat--Shamir proof.

The final theorem's remaining premises are explicit: matching field equations
on the stated support, absence from the four counted bad sets, and the
accepted round-boundary/final-pairing field equations. The support size is
not inferred merely from 22 successful queries. Turning false binding into a
small matching set and bounding the query event is the next probability step.

The six functionals are arbitrary supplied linear maps with derived weights.
The theorem does not identify Rust's weight constructors with these maps. It
also does not model proof bytes, parser/checkpoint provenance, hash binding,
random-oracle calls, semantic relation extraction, or a ZK simulator.

## Focused NUC verification

| Target | Successful attempt | Wall time | Peak RSS (KiB) |
|---|---|---:|---:|
| R1Line18Geometry | g | 27.76 s | 4694772 |
| R1ConcreteProjection | c | 1.31 s | 2761344 |
| R1FinalResponses | h | 1.52 s | 3143876 |
| R1SecondFoldMatched | b | 1.43 s | 3143856 |
| R1SecondFoldRestoration | m | 2.53 s | 2776208 |
| R1FirstFoldRestoration | e | 1.41 s | 2891880 |
| R1TwoFoldExtraction | f | 1.48 s | 3150380 |
| R1ConcreteBinding | c | 1.54 s | 3151312 |

Every selected target exited 0 with zero swap under MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0 and Lean's 5000 MB threshold. The printed
axioms for the binding theorem and its five cardinality theorems are exactly
`[propext, Classical.choice, Quot.sound]`. The extraction theorem has the
same axiom set. The scoped recursion-depth setting of 4096 handles the
symbolic composition; no large recurrence or generated certificate was
normalized, and no memory cap was raised.

Exact source hashes, outputs, failed attempts and source/receipt validation
are in `evidence/lean-concrete-extraction-20261013/`. Adjacent geometry,
final-response, first/second-restoration and import-rebuild folders contain
the dependent receipts. Twelve existing source files changed only their
import declarations; `import-only-review.json` records an independent
comparison against revision `2df5bf1a6f296a09cff71a886185112b66f0235a`.

These focused builds reuse a pinned cache. They do not constitute a full
release replay or complete historical source-to-object provenance audit.
Several existing cached declarations carried a generated SimplexCategory
Fintype instance for Fin; a specific Mathlib import restores that declaration
dependency. The repair is recorded without altering mathematical premises.
