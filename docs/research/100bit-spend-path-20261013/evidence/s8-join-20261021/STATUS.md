# S8 accepted-run join continuation

Branch `codex/cx-s8-join-20261021`, base `6c520f134`.
No shipped source edits. New Lean modules only. No pushes.

## Stage 1 — exact finish target

`S8JoinFinishExact.reference_exact` identifies the complete emitted owned
finish with the canonical raw prefix list; `mutable_exact` identifies the
complete mutable traversal with its exact transported list. The only
precondition is destination length ≤ raw length. Terms, phase, raw bounds,
callee success and congruence are not required for these execution identities.
`prefix_length` supplies length preservation of the deferred writes.

Focused receipts and failed intermediate attempts are retained in
`proofs/` and `manifest.json`. Failed elaborations may print `sorryAx`;
those are explicitly unsuccessful attempts, not accepted proofs.

## Upstream handoff

The current S7 branch was read with `git show`, without editing or importing
its working tree. At base `6c520f134`, `S7Kani3CallerTrace.reached_invariant`
consumes `PushTrace`; `p6_route_certificate` does not supply actual frozen
query membership or source state provenance. The requested next interface is
an actual reached raw vector, destination, and raw-coordinate congruence with
`∑ j : Fin 22, rho^j * basis q j l` (including saved-ten/resumed-twelve).

`dV_frozen` itself uses `D0TypedChecks.verify` with a `ClosedSum` field
predicate. It has no raw U64 Vec, mutable iterator or physical checkpoint
state. Such source-state provenance cannot be projected out of that model
without a concrete representation/reached-source construction. A new model
representation is not silently labelled the reached Rust state.

The compact strict scan is being joined to the exact canonical predicate
of `OraclePortCompactDraft`. It scans full 16-byte chunks and ignores a
trailing suffix, so a multiple-of-16 length condition is essential when
comparing with the parser's four-byte canonical scan.

## Stage 2 — exact byte/word grouping

`S8JoinCompactChunks.chunk_iff` equates the extracted strict codec on a full
16-byte chunk with the frozen parser's canonicality of exactly those bytes.
`canonical_chunks` proves the whole list/grouping equivalence for lengths
that are multiples of 16. No parser or codec operations are abstract callbacks.
All six theorem audits use standard axioms; focused attempt chunks-06 passes.
The retained coalesced R1SemanticHit/R0P caches resolve a duplicate-declaration
import failure in chunks-02; no shared cache or old module was modified.

## Stage 3 — total compact scan result

`S8JoinCompactTotal.check_values_total` proves full Result equality for every
extracted byte slice, including inner NonCanonical rejection and any ignored
partial final chunk. The target is canonicality of precisely the consumed
prefix, not an all-storage successful-input restriction. `aligned_scan_total`
uses the same frozen canonical predicate on the entire input when its length
is a multiple of 16. All five audits use standard axioms (scan-01).

`preflight.py` validates inherited S8 frozen file/reference hashes and the
new-module lexical scan. The historical checkers' broad-base failures are
recorded in `legacy-validation.json`; their code/old receipts are unchanged.

## Stage 4 — accepted frozen y1 scan

`S8JoinFrozenScan.accepted_y1` derives success of the complete emitted strict
scan on the actual 464-byte y1 slice (7031..7495) of the same stored byte
slice that dV_frozen accepts. Parsing supplies the canonicality and exact
length. No callee-success, codec, or S8 hypothesis remains. This covers the
single compact::check_values invocation in candidate::canonical_scan;
the other strict field decoders remain with their assigned cones.

`S8JoinScanRemainder.unaligned_mismatch` retains a four-byte invalid-tail
counterexample: the source chunks_exact scan succeeds but the whole-list
canonical predicate rejects. The total scan theorem models that behavior;
accepted y1 cannot hit it. All six audits pass with standard axioms
(frozen-scan-03, remainder-01). No shared cache or lock was removed.

## Stage 5 — exact field interpretation of finish

`S8JoinFinishField.modelValue_field` proves full-U64 reduction preserves the
exact QM31 tower value. `finish_field` and `mutable_field` identify the full
reference and mutable output field lists with the raw prefix. Their only
precondition is destination/raw length, independent of terms or phase.
All three final-source audits pass (field-04), standard axioms, zero swap.
This is field interpretation, not a proof of source query/TX provenance.

## Stage 6 — finalization at the frozen ClosedSum consumer

`S8JoinAccumulatorStage.finish_check` proves complete emitted finish plus
exact equality of the resulting check to the ClosedSum Boolean used by
D0TypedChecks, for arithmetic false results as well as true results. It
retains destination length=64, destination≤raw length and pointwise raw
field meaning as the S7 representation input. There is no successful helper,
phase, canonicality, residue-range or free S8 premise. The check expression
is a field reference; extracted finish_relation/dot and source caller
membership are not thereby proved.

Attempt accumulator-03 hit the default heartbeat bound comparing decision
instances. The replacement compares the underlying propositions, without
unfolding the finite-field decision and without changing limits. Final
attempt accumulator-05 passes (5.376s, 3,494,641,664-byte RSS, zero swap,
standard axioms). No unchanged heavy regression was retried.

## Stage 7 — canonical realization and committed S7 reference

`S8JoinModelRepresentation.model_caller` constructs the legacy P6 length and
coordinate-congruence interface at a canonical logical 64-row accumulator.
Its sum argument is the canonical coordinate of the field weight, not an
asserted equality to an independently supplied unreduced natural sum.
`model_finish_check` and `model_check_eq` prove complete emitted reference
finish and exact ClosedSum checking for every data/query/rho input.

`S8JoinS7Reference` imports the committed sibling
`S7JoinAccumulatorReference` at `939c74d63`, with source SHA and successful
receipt retained in `upstream-s7.json`. No sibling module was copied, edited,
merged or cherry-picked. Integration must include that committed dependency
closure. `weights_eq` identifies its produced weights with the frozen sums;
`reached_caller`, `finish_check` and `mutable_finish` supply P6 conditions and
complete finish at the canonical realization of that produced field state.
This is reference composition, not a source-storage/checkpoint identity.

Successful final-source checks: representation-02 and s7-reference-01, ten
standard-axiom audits, zero swap. The named upstream file was read only with
`git show`; the task uses its private cached object directory read-only.
