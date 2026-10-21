# Frozen-order cone audit — 21 October 2026

Statement-only audit of branch `codex/cx-cone-audit-20261021` at
`7edd598181856214a49f95e641073e6ed960dab1`, using
[the updated delivery table](JOIN-SPLIT-DRAFT-20261021.md) and
[the frozen-order target](FROZEN-ORDER-DRAFT-20261021.md).
Theorem names were searched in the branch's Lean sources, candidate sources,
and retained evidence sources; statements and relevant interface definitions
were inspected. No compilation, extraction, proof replay, or new axioms audit
was performed. Session A's pending re-pins are not assumed landed.

Classes: **(a)** source accepted-run equality against the matching frozen
stage, including ordered reads and complete outputs; **(b)** checked total
refinement on every value of the stated input type, allowing inner Rust
`Err`/`none`; **(c)** successful-input/domain-conditional facts whose hypotheses
must come from the caller; **(d)** the required source refinement is missing.
A total helper is labelled **(b), local** rather than credited to its entire
owner. Algebra/model facts alone are **(d)** for source refinement.

**No complete delivery-table cone has an instantiated (a) or (b) theorem in
the inspected snapshot.** The table distinguishes the best existing fragment
from that missing whole-cone join; a (c) fact may also need output-model
identification, not merely its precondition. None of the candidate sources
searched mentions `dV_frozen`, `AcceptedRunJoin`, `ConeJoin`, or `ConeLogJoin`.

The actual [decision](../lean/OraclePortFrozenOrderDecision.lean) is Guard,
`parseReached`, `queries`, the short-circuit list of `verifySlot_frozen`, then
`arithmetic`. There is no global Padding stage. S-cone numbering is not an
execution order. Preparation, transcript sampling, checkpoint and Pool facts
also need the surrounding `verifier D dV_frozen` driver/carrier bindings.
[OraclePortFrozenOrderJoin.acceptedRunJoin_of_total_cones](../lean/OraclePortFrozenOrderCones.lean)
requires actual `PerConeJoins`, S10 coverage and **both** source/model caller
identities. Its evaluation-only sibling `acceptedRunJoin_of_cones` additionally
requires enrichment stability; `ConeLogJoin` itself quantifies over every site,
argument and oracle world. These generic composition statements instantiate
none of the source cones below.

| Cone / frozen boundary | Strongest relevant existing statement(s), with file and theorem | Classification and exact scope | Still needed for the complete cone |
|---|---|---|---|
| **S1** — preparation/transcript driver; prepared claims/powers feeding arithmetic | [CurrentPreparedInstalledMeaning.lean](../lean-candidates/s1-prepared-installed-meaning-20261020/sources/CurrentPreparedInstalledMeaning.lean), `AspisR1ClaimPreparedBridge.InstalledMeaning.prepared_installed_meaning`; [LoopPowersEarlyTotal.lean](../lean-candidates/s1-early-return-powers-proved-candidate-20261020/sources/LoopPowersEarlyTotal.lean), `AspisR1LoopPowers.early_powers_total_exact` | **(c)**. Installed preparation success plus canonical inactive input gives gamma/kappa/alpha canonicality, original-payload claim meaning and all 29 scratch power meanings. `early_powers_total_exact` supplies successful powers and exact decoded values only under `Canonical x`, despite its name. | Concrete sampling/embed/hash callbacks; inactive provenance; full Prepared/scratch state and continuation equality; candidate-to-frozen source identity and caller composition. Whole-cone join **(d)**; Session A. |
| **S2** — dispatcher/adapter driver; header admission | [S2ObserverOffRepin.lean](../lean/S2ObserverOffRepin.lean), `AspisR1S2ObserverOff.first_success`, `first_eq_historical`; [OraclePortJoinSplitS2.lean](../lean/OraclePortJoinSplitS2.lean), `AspisR1.OraclePortJoinSplitS2.header_total`, `source_header_total` | **(c)** for the caller: successful first returns a decoder witness, reconstructed public value and successful observer-off child. `first_eq_historical` is unconditional Result transport, which may preserve outer failure. **(b), local** header reference for every `Usize × Bool × U8 × Bool`; `source_header_total` still assumes the all-input P6 header equality. | Actual byte/header binding, all first/tx2/authenticated children and error continuations, exact slices, source dispatch and AccountInfo adapter. Whole-cone join **(d)**. |
| **S3** — arithmetic row/group/`Weights::pair` | [S3ActualLoop0Outer12PrefixRetentionV1.lean](../evidence/s3-loop0-outer12-prefix-retention-v1-20261020/sources/S3ActualLoop0Outer12PrefixRetentionV1.lean), `AspisR1GroupedPairActualFieldOpsV3.ActualLoop0Outer12PrefixRetention.actual_grouped_success_supplies_prefix_and_outer_meaning`; [S3VariantInactiveComposition.lean](../lean-candidates/s3-s9-current-repin-20261020/s3-row-inactive-compose-v1-20261020/sources/S3VariantInactiveComposition.lean), `AspisR1.S3VariantInactiveComposition.s2_variant_row_inactive_grouped` | **(c)** for the grouped helper: `CanonicalLow low` and successful actual grouped call imply the 64-row coefficient-prefix meaning, canonical coefficients/output and exact outer-prefix decoded value. This is stronger than citing only row algebra. **(b), local** row/inactive composition on `Fin 64 × Fin 16`; [S3VariantRowCurrentSourceBridge.lean](../lean-candidates/s3-s9-current-repin-20261020/row-output-equation-v7-v1/sources/S3VariantRowCurrentSourceBridge.lean), `AspisR1.S3VariantRowAeneasCut.s2_row_result_value_current`, also covers every `Usize`. | Join low-array provenance, byte reads, grouped coefficient/outer result to the frozen arithmetic model and complete pair machine/post-state. Whole-cone join **(d)**; Session A. |
| **S4** — arithmetic four dots | [FourDotsFixedCallSuccessV1.lean](../lean-candidates/s4-four-dots-fixed-call-v2/sources/FourDotsFixedCallSuccessV1.lean), `AspisR1FastDotsFixedCallSuccessV1.fixed_success_calls_actual_helpers`; [S4OuterFoldTraceV2.lean](../evidence/s4-outer-fold-trace-v2-20261021/sources/S4OuterFoldTraceV2.lean), `AspisR1FastDotsOuterFoldTraceV2.actual_outer_success_exact_fold_sum`, `actual_outer_success_reducer_residue` | **(c)**. Fixed-call success exposes prefix extraction, all four actual one-dot calls and exact four-element output construction. Outer success plus all 29 coordinate bounds gives a seven-batch trace, at most four contributions per batch, exact limb sums and canonical reducer residues. Neither theorem establishes whole-call totality. | Derive coordinate/read/backend bounds from the reached caller; connect all four folds, limb conversions and final values to arithmetic; retain complete state and frozen pin. Whole-cone join **(d)**; Session A. |
| **S5** — arithmetic strict decode/tower/pairing/dot kernels | [Stage2FinishPairing.lean](../lean-candidates/s5-stage2-dot-residual-composition-20261020/sources/Stage2FinishPairing.lean), `AspisR1.Stage2FinishPairing.finish_pairingChecks`; [ActualDecodeKStrictQM31Parser.lean](../lean/ActualDecodeKStrictQM31Parser.lean), `AspisR1.ActualDecodeKStrictQM31Parser.source_refines`; [ExtractedCurrentReducer.lean](../lean/ExtractedCurrentReducer.lean), `AspisR1.ExtractedCurrentReducer.current_mul_mod`; [ExtractedCurrentQM31Exact.lean](../lean/ExtractedCurrentQM31Exact.lean), `AspisR1.ExtractedCurrentQM31Exact.current_qm_mul_exact` | **(c)** for finish/pairing and tower multiply: comparison/pairing laws, transcript reader, two-fold equation and successful finish, or canonical tower operands, remain premises. **(b), local** strict parser for every fixed 16-byte array, including rejection as `none`; M31 multiply for every stored U32 pair, with exact modular/canonical result. [OraclePortJoinSplitR22.lean](../lean/OraclePortJoinSplitR22.lean), `AspisR1.OraclePortJoinSplitR22.m31_multiply`, additionally proves local checked safety/wrapping equality. | Establish actual reached operands, raw/count bounds, optimized pair/dot/finish laws, operation order and frozen source/caller identity. Local arithmetic totality is not full S5. Whole-cone join **(d)**; Session A. |
| **S6** — decoder/public/tx1/checkpoint driver | [RepinS6First.lean](../lean/RepinS6First.lean), `AspisR1PublicPreparation.RepinS6First.first_success`, `reuse_decoded`, `first_eq_historical` | **(c)**. First success supplies exact decoder and successful tx1 witnesses; reuse needs a successful decoder equation. Historical equality is all-input transport with arbitrary tx1/error callbacks, not outer-success total refinement or equality to the frozen model. | Concrete tx1 and errors, proof/public slices, returned checkpoint bytes, state provenance and same-byte adapter binding. Whole-cone join **(d)**. |
| **S7** — arithmetic query values/geometry/inverses/batched accumulation | [S7JoinFrozenConsumer.lean](../lean/S7JoinFrozenConsumer.lean), `decision_eq`, `accepted_matching_query`; [S7JoinBasisCanonical.lean](../lean/S7JoinBasisCanonical.lean), `total_exact`; [S7JoinGeometryGroups.lean](../lean/S7JoinGeometryGroups.lean), `inversion_groups`; [S7JoinBackendCarriers.lean](../lean/S7JoinBackendCarriers.lean), `multiply_exact`, `canonicalize_exact`; [S7JoinAccumulation.lean](../lean/S7JoinAccumulation.lean), `total_exact` | **(b), local/reference:** total full-program equality of the S7 field-reference replacement with `dV_frozen`, including the original reader, rejection and ordered reads; accepted reference check on the identical reached query vector. Actual emitted initialized width-64 basis has exact naturalLineValue semantics and all 256 words canonical, for arbitrary input U32. Emitted prefix/backward/group Vec loops plus the guarded fixed-chain inverse port give exact reciprocal records in ordinal order, under nonzero decoded inputs, length/allocation bounds and supplied gathered storage. Lossless four-lane adapters connect canonical owned operands to frozen QM31 arithmetic. The total observer-off owned accumulator port derives the initialized basis, all 64 pushes and PushTrace membership, exact natural-basis coefficient updates, terms/RHS/power/next effects on its canonical/reached-phase domain; initial raw phase is derived for arbitrary U32 limbs. **(c)** original constructor/helper witnesses remain; these local results do not instantiate the frozen query/TX caller. | Whole-cone join **(d)**. Bind frozen `for_range` gather/zero/iterator/allocation, literal table operations and opaque inv to the checked ports (R17 numeric entries are externally certified; kernel hA/hB remain named). Bind opening/four_dots and source `query_values`/`accumulate_batched_with_node`, the original 64-row/phase/power/rhs/next/trace callers to the total owned port and both TX PushTrace memberships; physical ABI, observer/source/P6 and runtime provenance remain. No headline premise deleted. Focused union and exact receipts: `evidence/s7-join-20261021/`. |
| **S8** — arithmetic accumulator, residue traversal and compact checking | [S8FrozenRow.lean](../lean/S8FrozenRow.lean), `S8FrozenRow.row_step_total`; [OraclePortJoinSplitS8.lean](../lean/OraclePortJoinSplitS8.lean), `AspisR1.OraclePortJoinSplitS8.row_total`; [EbyKFinishTotal.lean](../lean-candidates/eby-k-finish-total-source-20261020/sources/EbyKFinishTotal.lean), `AspisR1EbyKFinish.Proof.eby_finish_entry_total` | **(c)** row fact: iterator next, index/read witnesses, canonical limb/basis and raw cadence are required. `RowArgs` repackages them; it does not discharge them. The conclusion gives row-body success and product equality, not a full accumulator-state equation. **(b), local** EbyK finish entry succeeds on every typed accumulator and returns the eight reduced canonical limbs. | Whole new/value/finish and Vec/iterator simulation, residue state meaning, strict compact scan, final flush and both caller writes; identify the finish helper with actual reached source. Whole-cone join **(d)**. |
| **S9** — arithmetic factored Libra weights | [S3S9CurrentSourceModel.lean](../lean-candidates/s3-s9-current-repin-20261020/S3S9CurrentSourceModel.lean), `AspisR1.S3S9CurrentSourceModel.old_s9_weight_eq_factored`, `s9_source_weights_equal`; [S2LibraFactoredIdentity.lean](../lean/S2LibraFactoredIdentity.lean), `AspisR1.S2LibraFactoredIdentity.source_scaled_eq` | **(d)** source refinement. These are generic semiring identities over `Fin 4` weights/scaling, not equations for the checked extracted factored machine. No Result success, mutable state or source execution occurs in the cited conclusions. | Current low/high powers and weight-loop simulation, operand canonicality and caller/model connection, adopted source pin. Session A. |
| **S10** — all sites and all continuations, including errors | [OraclePortS10ModelInventory.lean](../lean/OraclePortS10ModelInventory.lean), `covered`, `inventory_nodup`, `model_S10Join`, `interpret_eq_frozen`; [frozen inventory report](S10-INVENTORY-20261021.md), [machine reconciliation](../evidence/s10-inventory-20261021/inventory.json) | **(b), model stage only**: concrete five-site `S10Join` covers every continuation and interprets exactly to `dV_frozen`; it does not cover nested implementation bodies or the outer driver. **Whole-source (d)** remains: pinned ELF/direct-LLBC census and source hashes are checked, with explicit unassigned/error/indirect/inline frontiers. Counts are evidence records, not independent proof obligations. | Obtain clean deployed-target entrypoint extraction for default/devnet/Pool, resolve every indirect and inlined/monomorphized source instance, secure cone-owner acceptance, construct the actual frozen source tree and source/model ordering joins. Trusted specifications remain explicit residuals. Generated naming changes remain proposed for cone-owner adoption. S10 inventory worker; S1–S6/S9 and all other owners retain their modules. |
| **Parser / compact codec** — `parseReached` (and source compact expansion/strict scan) | [OraclePortStoredParserC4.lean](../lean/OraclePortStoredParserC4.lean), `AspisR1.OraclePortStoredParserC4.parsed`, `parse_of_parts`; [OraclePortCompactDraft.lean](../lean/OraclePortCompactDraft.lean), `AspisR1.OraclePortCompactDraft.parse_header`; local fixed-field `ActualDecodeKStrictQM31Parser.source_refines` above | **(d)** for whole source parser/codec. `parsed` assumes model `parseReached = some p` and yields model parse/alignment; `parse_of_parts` assumes header, canonical scan, semantic rows and alignment. Neither compares extracted scanning/parsing to the model. **(b), local** only for the fixed 16-byte field decoder, not arbitrary stored slices. | All offsets/length/canonical guards, scanner/semantic rows/compact expansion and exact rejection Results; construct decoder D binding and stored-to-reached projection. |
| **Multiproof** — six short-circuited `verifySlot_frozen` programs | [R13CloseDedup.lean](../lean/R13CloseDedup.lean), `AspisR1Stage2.R13Close.Dedup.dedup_step_pairs`; [R13CloseLevelRun.lean](../lean/R13CloseLevelRun.lean), `AspisR1Stage2.R13Close.Level.binary_loop_write_fold`; [OraclePortFrozenOrderSlotPath.lean](../lean/OraclePortFrozenOrderSlotPath.lean), `AspisR1.OraclePortFrozenOrder.slot_path` | **(c), local** source facts: successful dedup step preserves exact pair support; successful binary level loop expresses arrays as a write fold. **(d)** for source-to-frozen slot refinement. `slot_path` gives an indexed root witness and containment in the accepted **model** log, not equality to extracted execution. Old recursive `execute_trace`/root facts do not target this schedule. | Sorted leaf/duplicate scan, post-leaf padding and node consumption, safe live-array overwrite, all 18 ascending levels/parents, byte adapters and exact ordered digest reads, then six-slot caller composition. No permutation to the recursive log is required. |
| **Checkpoint ABI** — writer/resume driver and prepared/accumulator bytes | `OraclePortCkptAbi2Unwrap.raw_panic_unreachable` / `savedTen_panic_unreachable`; `OraclePortCkptAbi2Reached.accepted_inputs` / `accepted_reference_resume`; `OraclePortCkptAbi2Vec.append_exact`; linked Kani `proofs::frozen_writer_exact_byte_and_reads` and four field-codec roots. See [continuation status](../evidence/ckpt-abi2-20261021/STATUS.md). | **(b), local** checked raw reads, bounded-list Vec content and reached-model save/resume; **P6, bounded** frozen writer byte/digest-call equality (S2, next=10, 64 weights, proof/public lengths 3/5). Whole-cone **(d)** remains. No concrete `AcceptedRunJoin` or full reader theorem is supplied. | Complete frozen reader/codec adoption and kernel byte-model identification; arbitrary proof/public lengths; Rust Prepared/query-loop/pending-finish provenance; physical allocation/owned iteration; actual stage-1/stage-2 entry/driver identity with all checkpoint reads. Runtime same-snapshot binding remains separate. |
| **Pool caller / ASQ8** — external handoff to verifier driver | [OraclePortJoinSplitASQ8.lean](../lean/OraclePortJoinSplitASQ8.lean), `AspisR1.OraclePortJoinSplitASQ8.pool_handoff`; [ASQ8Normalization.lean](../lean/ASQ8Normalization.lean), `AspisR20Request.ASQ8Normalization.success_bytes`; [ASQ8PoolHandoff.lean](../lean/ASQ8PoolHandoff.lean), `AspisR20Request.ASQ8PoolHandoff.handoff_bytes` | **(c)**. `pool_handoff` assumes all-input `P6Normalization source`, successful normalization and a four-byte hint suffix, and proves extracted stripping returns the normalized body. `success_bytes` is identity after reference normalization success. Retained full-Result Kani normalization equivalence supports the named P6 boundary, not a Lean full Pool total-refinement theorem. | CPI program/accounts/payload, PDA/ownership/AccountInfo guards, public reconstruction for both variants, checkpoint/proof/public same-snapshot and transaction order. Whole-cone join **(d)**; ASQ8 is 320 bytes, reconstructed ASF8 1880 bytes. |

Local **(b)** results supply local R22 only through the checked operational/source
translation boundary. For example,
[R22TotalRowCones.row_inactive_R22](../lean/R22TotalRowCones.lean) and
[R22TotalCoreCones.strict_field_parser_R22](../lean/R22TotalCoreCones.lean)
retain explicit `Translation` arguments. M31
[R22TotalReducerExecution.multiply_R22](../lean/R22TotalReducerExecution.lean)
has the concrete operational connection already proved. Result transport,
model equations, a successful wrapping computation or a final Bool equation
alone do not establish whole-cone R22 or accepted ordered-log equality.

Cheapest next three complete-cone attempts (relative judgment from signatures,
not measured proof estimates):

1. **S9:** attach the existing factored semiring identity to the current small
   low/high power and four-output loops. The mathematical identity is already
   available; the remaining task is checked machine/operand/caller refinement.
   Keep Session A's source pin authoritative.
2. **S3:** extend the existing actual grouped prefix/outer meaning through the
   full pair caller. Row/inactive semantics are already total locally and the
   stronger successful-helper statement retains coefficient meaning; derive
   `CanonicalLow` from reached preparation and identify the exact model output.
3. **Checkpoint ABI:** connect the fixed-layout writer/resumer to the C5 byte
   model, using existing source digest-call witnesses and model roundtrips.
   This is a bounded serialization/state simulation without S7's dynamic
   inverse construction or the multiproof's 18-level mutable-array schedule.
   Source byte provenance and ordered calls remain mandatory; runtime sameness
   is a separate obligation.

## Checkpoint ABI worker addendum — 21 October 2026

Draft on `codex/cx-ckpt-abi-draft-20261021`; no source adoption, merge or
premise removal. The original table's whole-cone classification remains open.

| Cone | New checked statements | Updated classification | Remaining complete-cone obligation |
|---|---|---|---|
| Checkpoint ABI | `OraclePortCkptAbiSourceFields.successful_fields`: all emitted resume Prepared/Accumulator outputs, 22 query reads, validation, semantic-alpha/weights inputs, allocation, final cursor and saved-next cast have producing-call witnesses. `OraclePortCkptAbiSourceBacking.all_fields_same_backing`: all 16 field cursor boundaries retain the same checkpoint under atomic reader-preservation contracts. `OraclePortCkptAbiReader.raw_total_exact` and `OraclePortCkptAbiReadSequence.savedTen_reads_total`: total checked raw-body simulation with exact bytes, immutable backing and final offset 1736, under unwrap-on-Ok. `OraclePortCkptAbiCodec.decode_encode`: total saved-ten reference result including duplicate rejection. `OraclePortCkptAbiReference.accepted_saved_fields` / `writeResume_trace`: complete reference fields, reached-ten/resumed-twelve state and exact six ordered digest reads. | **(c), source fragments** for successful emitted resume and atomic reader contracts; **(b), local/reference** for total saved-ten Option codec and raw-read schedule. **Whole-cone (d)** remains. Reference results are not relabelled frozen source refinement. | Instantiate the concrete current `ResumeOps`/unwrap and field-codec laws; prove frozen writer bytes equal the reference and reached prepared/query/accumulator provenance; allocation/owned-Vec and both caller identities; assemble the driver checkpoint site and source adoption. `dV_frozen` itself contains no checkpoint stage. Same-snapshot runtime binding remains separate. |

The attempted unconditional C5 resumer substitution is **false on rejection
paths**: `OraclePortCkptAbiRejection.c5_eager_log_mismatch` proves one versus
three reads after a failed proof digest. The new reference short-circuits
proof, public and checksum comparisons, and its exact `resume_eval` handles
all inputs. It specializes S2 saved.next=10; it does not claim to model every
other next value accepted by Rust resume. Repeated model queries reject;
uniqueness must be supplied by reached source sampling/caller provenance.

The retained R22 Kani raw-reader contract establishes cursor bounds and
canonicality, but does not state byte-value equality. The existing Lean raw
body abstracts the debug-bearing unwrap because the emitted concrete debug
instance depends on a nonstandard Formatter axiom. This packet retains that
boundary and uses only standard axioms. R9's codec is explicitly logical,
not the physical 1768-byte ABI. No complete existing physical codec theorem
was found in the inspected R9/R22/source proof inventory.

Evidence and reproducible focused audits:
`evidence/ckpt-abi-draft-20261021/manifest.json`, `STATUS.md`,
`source-pins.json`, `audit-result.json`; run
`python3 -B tools/oracle-port-ckpt-abi/generate.py --check` and
`python3 -B tools/oracle-port-ckpt-abi/audit.py`.
R19 and the frozen headline are byte-identical to the base; both retained
signature diffs are empty. This records **zero** premise deletions, rather
than claiming that the missing source join has been discharged.

## Checkpoint ABI continuation — 21 October 2026

Branch `codex/cx-ckpt-abi2-20261021` links the actual unmodified verifier in
its Kani proof crate. Four field-codec contracts and a symbolic-byte writer
comparison passed. The writer checks all output bytes and all checksum-body
bytes by independently arbitrary indices, with exact three-call hash order.
The precise bounded domain and fixed proof/public lengths are recorded in
`tools/oracle-port-ckpt-abi2/README.md`; no all-length or whole-cone claim is
made. Pinned Charon/Aeneas extraction of the sparse byte reference succeeds.

The Formatter boundary is isolated by a kernel proof that any panic
continuation is unreachable on the complete bounded saved-ten raw schedule.
Acceptance of `dV_frozen` supplies query uniqueness and its model recurrence
inputs, rather than an externally chosen query function. Rust preparation,
query-loop and pending-weight-finish identification is still required. The
bounded-list Vec model gives exact push/append content, not physical allocator
availability, Drop, or a source-owned iterator theorem.

Broad reader composition attempts, including verified decoder adapters,
remain unproved after capped timeouts. They are retained as diagnostics,
not counted as successful contracts. No failed proof's recovery axioms are
accepted. The complete stage-1/stage-2 driver is not instantiated.
`OraclePortCkptAbi2DriverObstruction.checkpointThen_not_erased` proves that
inserting authentic write/resume before an unchanged tail preserves its Bool
but adds six reads; this particular erasure cannot discharge the ordered-log
join. It is not a counterexample to an independently constructed full frozen
Rust/model driver identity. The cone stays **(d)** and no headline premise is
removed. No shipped source changed, so the conditional ELF rebuild gate was
not triggered. Complete receipts are under `evidence/ckpt-abi2-20261021/`.
