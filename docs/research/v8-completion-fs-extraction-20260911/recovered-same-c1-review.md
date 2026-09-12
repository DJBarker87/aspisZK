# Computed components to the same C1 payment table

`lean/RecoveredSameC1Transfer.lean` is a draft awaiting its focused build.
It imports the existing final-only fork interpolation and selected transfer
facts, without changing either source.

The new first connection is deterministic: the C1 projection of
`recoveredComponents` is proved to belong to the pre-lambda C1 family. Under
the explicitly required base-valued C1 oracle premise, its decoded base table
lifts back to the very same first sixteen recovered columns. The three C1
claim rows are consequently the actual covectors of that table, not of an
independently supplied candidate. No row or Poseidon residual is inferred
from that claim equality.

The conditional transfer endpoint computes its copy helper as recovered
lane26. The actual producer's C2 order is `[h, masks.g, d]` in
`payment_extraction.rs:285–290`; it is not a freely chosen second helper.
Given the separately exposed residual conditions, the existing selected copy
theorem produces either aliases or the existing lambda/chi collision event.
The alias branch then produces transition facts, actual raw direction/index
decoding, the reconstructed public forest root and the same-key nullifier.
No validator success or valid-witness predicate appears in the premises.

## Exact remaining premises and producers

1. **Fork availability:** 29 gamma nodes, four alpha nodes each, and
   `RecoveredMiddleFork` at all 116 continuations. This is stronger than one
   acceptance or arbitrary `RecoveredHigh`: its middle upper bound and
   recovered-family membership are not removed. A bounded legal collector
   and its success/error accounting remain missing.
2. **One fixed family of cardinality at most one:** required by the existing
   computed-membership theorem; the general cardinality-100 family result
   does not discharge it. No existence follows from uniqueness alone.
3. **Base-valued fixed C1:** authenticated canonical full-word recovery must
   produce this property. Canonicality of a few openings is insufficient.
4. **Literal point functionals:** `e.weights` must be instantiated by the
   actual three source MLE rows. The new theorem preserves these exact
   covectors; it does not certify their source producer by naming them.
5. **RowsVanish on the computed table:** an explicit universal selected-row
   predicate, including positive-transfer position94, not a supplied
   verifier-success flag. It still needs semantic algebraic/batching
   soundness and the actual early-C1/source coupling.
6. **PoseidonChecks on the same table:** exact mathematical hash-round
   constraints. Neither the 87 point claims nor canonical base descent
   establishes them. Their source/constant-table correspondence remains.
7. **CopyConditions on computed lane26:** the actual selected Boolean copy
   equations, total helper sum, inactive helper sum, and all active-row
   slot poles. They remain explicit; the deterministic row-shift repair
   does not by itself imply these global equations.
8. **Public SourceComparisons and exact carry:** caller/account authority,
   sequence/index checks and the Rust carry-index computation remain source
   obligations. No prover-supplied context is designated authenticated.

The first theorem closes a concrete same-table ambiguity before item5; the
second states what items5–8 buy while preserving the copy-collision branch.
This is not an executable checked-payment extractor or a new numerical
soundness bound. Noncomputable interpolation/family existence does not supply
allowed oracle access, runtime, or universal extraction success.
