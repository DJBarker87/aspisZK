# J1 relation statement and model boundary

Lead statement following `LEAD-DECISIONS-20261015.md`. The implementation is
being checked in focused targets; this document is not a completed J1 result.

`SpendRelation.Wspend` contains three integers below `2^30`, the input key and
salt, the 24-step private path, the ordered pair and its occupancy witness,
and recipient/change owner and salt data. All field coordinates in this
concrete witness use M31. A generic `Witness K` is retained only to reuse the
existing algebraic extraction theorems.

`Rspend pub w` checks canonical variant/option shape, the existing
`InputWitnessCore.Relation`, integer conservation, the change commitment and
the variant-specific recipient commitment or withdrawal amount. The input
relation explicitly ties the selected occupied pair slot and its first
sibling to the same note whose key/salt produce the nullifier and whose
24-step path produces the public anchor. Thus it includes knowledge and
membership equations, rather than just existence of an unrelated valid note.

The checker is a finite Boolean calculation over the supplied witness;
`check = true ↔ Rspend` is now proved without using classical choice in its
executable definitions. The R0 `paymentWitness` clause is reused by deriving
`InputNoteExtracted pub A` for the same input value, not by deciding its
existential quantification through enumeration. The checked production
bridge constructs the witness from the existing trace key, salt, path, pair,
output-note and bounded-value theorems, under the explicit canonical-option
premise. Both `R1SpendRelation` and `R1SpendRelationExtraction` passed their
focused NUC compile and axiom audits.

The next checked bridge, `ConcreteSpendExtraction.candidate_checked_witness`,
now produces an M31 witness accepted by `checkM31` from a candidate of the
typed recovered word, canonical public options, and that candidate's
production/copy-link facts. `CandidateBaseProjection` reuses the existing
subfield descent to obtain trace typing; `TraceSpendWitness` proves all
selected witness coordinates belong to the embedded base.
`SpendRelationMap.rspend_map_iff` transports the complete relation through a
field embedding, and `SpendBaseDescent` uses explicit coordinate projection
only on those base-typed coordinates. The combined theorem is existential:
the old trace path selector is noncomputable, and neither accepted-proof
recovery nor an efficient list decoder is established by it. Executable
reconstruction is being checked separately.

The current production value theorem permits zero values. Accordingly this
semantic relation uses bounded nonnegative values; the source's honest
pair-forest preparation additionally requires positive input and output
values. This difference is explicit and no equivalence to that stronger
preparation checker is claimed. Public withdrawals must be nonzero through
canonical option validation. A strict-positive protocol claim would require
the missing production implication or a verifier change.

The public carrier here is the semantic `R0P.Public`; the ASF8/payment byte
decoder, its mapping to that carrier, candidate recovery, account binding and
checkpoint/proof immutability assumptions remain separate J1/J2 obligations.
The legacy depth-20 payment relation is not used as the current 24-direction
pair-forest relation. Freshness, custody and the append transition remain in
the settlement release gate specified by the lead decisions.

The probability route follows the merged design: idealized word messages
first, then the Merkle compiler outside the combined hash event. Its full
experiment ledger uses `Q * epsilon + 12 * Q^2 / 2^256`, with the combined
event charged once. The earlier pure-wrapper `3 * Q^2` formula has a narrower
scope. The separate Las Vegas extraction allowance is at most `2^-120` and
is not yet a proved or implemented extraction guarantee.
