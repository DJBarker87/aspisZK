> R1 update (2026-10-20): the R1 pair-forest marker path is no longer the
> nullifier-marker PDA path described below. B1 uses `create_with_seed` under
> the forest master; see [the accepted B1 review](LEAD-REVIEW-POOL-B1-20261019.md)
> and its freshness premise. Historical results and legacy PDA routes are unchanged.

# J1 relation statement and model boundary

Lead statement following `LEAD-DECISIONS-20261015.md`. The implementation is
being checked in focused targets; this document is not a completed J1 result.

`SpendRelation.Wspend` contains three integers below `2^30`, the input key and
salt, the 24-step private path, the ordered pair and its occupancy witness,
and recipient/change owner and salt data. All field coordinates in this
concrete witness use M31. A generic `Witness K` is retained only to reuse the
existing algebraic extraction theorems.

`Rspend pub w` checks canonical variant/option shape, the existing
`InputWitnessCore.Relation`, integer conservation, the change commitment, the
variant-specific recipient commitment or withdrawal amount, and the
witness-free `SpendRelation.AppendBinding` conjunct. `AppendBinding` binds the
public next root to the append path for the selected output pair and binds the
carry frontier cell when the carry is below 20. Its executable Boolean check
is the final `appendCheck` conjunct in `SpendRelation.check`; the equivalence
`check = true ↔ Rspend` is proved by `check_eq_true_iff`.

The input relation explicitly ties the selected occupied pair slot and its
first sibling to the same note whose key/salt produce the nullifier and whose
24-step path produces the public anchor. Thus it includes knowledge and
membership equations, rather than just existence of an unrelated valid note.

The checker is a finite Boolean calculation over the supplied witness;
`check = true ↔ Rspend` is proved without using classical choice in its
executable definitions. The R0 `paymentWitness` clause is reused by deriving
`InputNoteExtracted pub A` for the same input value, not by deciding its
existential quantification through enumeration. The `SpendRelation` and
`SpendAppendBinding` targets passed focused compilation and axiom audits.
The core production-trace bridge `SpendRelationExtraction.of_production`,
including the append correction, has also passed its focused compile and
axiom audit. The downstream M31/executable bridges have separately passed
their focused refresh against the six-conjunct relation.

The downstream M31 bridge is `ConcreteSpendExtraction.candidate_checked_witness`:
its intended inputs are a candidate of the typed recovered word, canonical
public options, and that candidate's production/copy-link facts, with an
M31 witness checked by `checkM31` as its result. The separately checked descent
components use `CandidateBaseProjection`, `TraceSpendWitness`,
`SpendRelationMap.rspend_map_iff`, and `SpendBaseDescent`; the combined theorem
is existential, and the old trace path selector is noncomputable. Neither
accepted-proof recovery nor an efficient list decoder is established here.
`ComputableTraceWitness`, `TraceValueDecode` and `TraceWitnessExtract` now
provide executable reconstruction from a supplied trace. The extractor
returns only checked witnesses and succeeds under the same explicit
production/base-typing premises. `ListWitnessExtract` scans a supplied list
and bounds candidates inspected by its length; it does not supply that list
or prove the full-log extractor's polynomial cost or failure allowance.

The current production value theorem permits zero values. Accordingly this
semantic relation uses bounded nonnegative values; the source's honest
pair-forest preparation additionally requires positive input and output
values. This difference is explicit and no equivalence to that stronger
preparation checker is claimed. Public withdrawals must be nonzero through
canonical option validation. A strict-positive protocol claim would require
the missing production implication or a verifier change.

The public carrier here is the semantic `R0P.Public`. The section-9 byte
model now has exact decoding/encoding and a unique accepted byte list for
every canonical M31 public record with index below `2^64`, as proved in
`SemanticPublicCodecComplete`. Its projection preserves all public fields,
and its length lemmas discharge the modeled initialization frame bound.
The separate ASF8/payment byte
decoder, its mapping to that carrier, candidate recovery, account binding and
checkpoint/proof immutability assumptions remain separate J1/J2 obligations.
The legacy depth-20 payment relation is not used as the current 24-direction
pair-forest relation. The root and carry equations are now part of `Rspend`;
the frozen table's tree meaning and chronological frontier invariant remain
release gates, alongside freshness, anchor history, live-state matching and
custody, as specified in J1.R3.

For J1.R3's remaining `NonCarryShape` check, the current R1 split reaches the
full host comparison during stage one: adapter `stage1` accepts `[3,10]` or
`[3,11]` and calls `super::first`; that calls `verifier::tx1`, which calls
`r1_semantic::verify_observed`. Before tx1 processes its first `k` queries or
writes its checkpoint, `verify_observed` calls `Public::terminal_qm31`,
through `terminal_parts` and `composition_parts`, where
`validate_transition` compares every non-carry active after-frontier cell
against the snapshot frontier and checks the other required empty cells. The
carry cell is skipped there and is bound by the production proof. This
path is reached for the adopted 10/12 split because the stage-one instruction
passes `k = 10`; stage two resumes the checkpoint and finishes queries but
does not repeat semantic parsing or `validate_transition`.

The Pool program's persistence-side `next_pair_forest_lane_v1` check remains
narrower: it checks index increment and after-frontier entries at zero bits
of the new index against the empty-root table, but does not compare active
one-bit entries against the snapshot frontier. That program-side check is a
separate call path from the reachable tx1 host verifier check. The current
inventory records source reachability only; it does not claim a Rust-to-Lean
refinement for either path.

The probability route follows the merged design: idealized word messages
first, then the Merkle compiler outside the combined hash event. Its full
experiment ledger uses `Q * epsilon + 12 * Q^2 / 2^256`, with the combined
event charged once. The earlier pure-wrapper `3 * Q^2` formula has a narrower
scope. The separate Las Vegas extraction allowance is at most `2^-120` and
is not yet a proved or implemented extraction guarantee.
