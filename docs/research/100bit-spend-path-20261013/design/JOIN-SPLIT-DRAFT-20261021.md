# Execution join split — draft, 21 October 2026

Branch `codex/cx-join-split-draft-20261021`, base `3a01b2d6d`. This
additive packet depends on the **unmerged** oracle-port draft. It is not
approval of that port and must not be merged before the user's approval.
Only new `OraclePortJoinSplit*` Lean modules are authored. Session A's
S1/S3/S4/S5/S9/S10 candidates, the sibling `OraclePortRowAware*` modules,
existing Lean modules, M10 instrumentation and shipped sources are read-only.

## Stage 1: total replacement interface

`OraclePortJoinSplitCore` defines thirteen executable cone owners and a
separate S10 call-site coverage predicate. An invocation is indexed by its
owner **and declaration name** and has dependent argument/result types.
Those types must preserve every mutable pre/post-state component and ordinary
Rust rejection. `Calls` preserves nested/repeated calls, return-dependent
branches and explicit oracle reads. It imposes no fictional chronological
ordering S1 → S2 → … → Pool; the frozen callers determine that order.

The exact all-input obligation for every executable cone `c` is:

```lean
∀ site, site.owner = c → ∀ args, source site args = model site args
```

Both sides are complete `Program Bytes State (σ.Value site)` values.
`PerConeJoins` names all thirteen obligations. `interpret_eq` proves their
substitution through the whole ordered, branching caller. `S10Join` requires
every invocation in every continuation to occur in the supplied inventory.
It intentionally adds audit coverage, not an extra execution stage.

`executionJoin_of_cones` derives the **unchanged** `ExecutionJoin D rust`
from those joins, S10 coverage and the explicit composition/ordering join:

```lean
source_order : ∀ i, rust i = interpret source (tree i)
model_order : ∀ i, interpret model (tree i) = verifier D dV i
```

The tree, signatures, implementations and inventory are parameters, not
constructed frozen artifacts. These two identities remain substantive caller
obligations. In particular, `model_order` must account for the port's extra
checks, early returns, duplicate handling and oracle reads, not merely prove
the same accepted-input arithmetic predicate. No frozen `ExecutionJoin` is
claimed by this substitution theorem alone.

Stage 1 focused compile: `OraclePortJoinSplitCore`, attempt 1, exit 0,
4.289 seconds, 3,659,743,232-byte peak RSS, zero swaps. All three theorem
audits use standard axioms only. Exact source/import hashes, revision,
command, output and timing are under
`evidence/join-split-draft-20261021/`; `manifest.json` records every attempt.

## Concrete decision stages and certificate adapters

`OraclePortJoinSplitDecision` spells out the six **actual** dV stages:
Guard, `parseReached`, `queries`, Padding, `verifySlots p q slots`, and
`arithmetic`. `model_eq` proves that this skeleton is exactly dV on every
stored input/prefix/message. `StageJoins` requires total equality of each
stage; `decision_eq` composes them. `executionJoin` additionally requires
`DriverJoin`: the frozen transcript driver is the decoder/sampler driver
using those stages. This is the concrete target of `model_order`, not an
assertion that S1–S9 occur in numerical order in dV.

The full verifier target also contains the outer transcript, decoding and
sampler operations. Pure checks cannot invent the source's checkpoint hash
calls or erase them. All such reads and early-return branches belong in the
ordered tree/driver proofs. In particular, equality only of `eval`'s final
Bool, or equality only on accepted executions, does not meet `ExecutionJoin`.

### Exact cone delivery table

Here `J(c)` is **verbatim** the all-input `ConeJoin` formula above with
`c` specialized to the indicated constructor. For a checked pure owner,
the total-form deliverable is
`∀ x, extracted x = Aeneas.Std.Result.ok (model x)`;
the model value includes inner Rust `Err`/`Option.none` on rejected input.
`Args`/`Value` are an uninstantiated dependent interface, not guessed
concrete Rust carriers. The following table fixes which actual owners and
state must instantiate it; `inherited-owner-signatures.json` quotes nine
representative existing signatures verbatim and pins their read-only files.
No pending re-pin is silently treated as a landed implementation of `J(c)`.

| Cone | Exact total join / required source state | Already proved; exact theorem or certificate | Remaining / owner |
|---|---|---|---|
| S1 | `J(.s1)`: gamma powers, `Prepared`, scratch `[E;29]`, semantic challenges/claims and complete tx1 preparation body; preserve hash continuation and every field | `AspisR1LoopPowers.early_powers_total_exact` has canonical-x antecedent; `AspisR1ClaimPreparedBridge.InstalledMeaning.prepared_installed_meaning` derives claim/power meaning from **successful** installed prepare plus inactive canonicality | Total concrete callbacks, inactive provenance, powers/preparation/caller composition, adopted source identity. **Session A** |
| S2 | `J(.s2)`: observer off, first/tx2/authenticated dispatch, exact slices and all child failures; no observer trace substituted for oracle trace | `AspisR1S2ObserverOff.first_eq_historical`, `first_success`; linked `header_correspondence` / `non_s2_rejected` Kani roots; new `OraclePortJoinSplitS2.header_total` gives exact all-input extracted header result | Complete child implementations, source header→stored/public-tag binding, AccountInfo/adapter caller, rejection timing; S2 + adapter owners, P2/P2′ |
| S3 | `J(.s3)`: row map, group table/mask bits and the full grouped `Weights::pair` state/loops | `AspisR1.S3VariantInactiveComposition.s2_variant_row_inactive_grouped` is total on `Fin 64 × Fin 16`; `S3S9CurrentSourceModel` supplies source-shaped table/group algebra | Full optimized grouped-pair machine, real field/read callbacks, canonicality, frozen pin. **Session A** |
| S4 | `J(.s4)`: four output dots, complete raw/limb/batch state, prefix reads and helper calls | `AspisR1FastDotsFixedCallSuccessV1.fixed_success_calls_actual_helpers` starts with successful `four_dots_fixed`; outer-fold/limb/canonicality lemmas are conditional | Whole-call totality from independent source bounds, seven-batch cadence, real backend and exact source outputs. **Session A** |
| S5 | `J(.s5)`: strict field decode, pairing and dot kernels, operation order and final values | `AspisR1.ActualDecodeKStrictQM31Parser.source_refines` is total on `[U8;16]`; `ExtractedCurrentReducer.current_mul_mod`; `ExtractedCurrentQM31Exact.current_qm_mul_exact` needs canonical operands. New `OraclePortJoinSplitR22.m31_multiply` instantiates exact wrapping/canonical result for **all stored U32 pairs** | Actual reached tower operands, raw/count bounds, optimized pair/dot/finish and callers. **Session A** |
| S6 | `J(.s6)`: `first`/`first_decoded` decoder/public/proof/k and error callbacks, plus exact returned checkpoint bytes | `AspisR1PublicPreparation.RepinS6First.first_eq_historical`, `first_success`, `reuse_decoded`; R15 read/write source-map audits | Actual concrete downstream tx1/errors; account proof suffix/public bytes and same-byte checkpoint caller binding. S6 + adapter owners, P2/P2′ |
| S7 | `J(.s7)`: production `candidate::query_values`, `accumulate_batched_with_node`, geometry constructor/readers, full 64-weight Vec, basis/raw/terms/rhs/power/next/trace state | 30 retained Kani roots cover scalar/frame/grouping cuts; `S7OwnedP6ScalarProof.scalar_eq_source_push`, `S7OwnedP6RowContract.source_eq_batched_model`, `S7OwnedP6LoopSimulation.simulation`, `S7OwnedP6QueryRead.selected_inverse`; new `OraclePortJoinSplitS7.residue_total` / `row_join` apply the exact local scalar/row facts | Construct inverse vector, prove zero/prefix/backward/grouping loop simulation and lengths; basis/block/Vec invariants, real backends, query/caller composition. **S7 owner**, not Session A |
| S8 | `J(.s8)`: accumulator new/value/finish, residue phases and row traversal, `compact::check_values`, both callers and exact finish result | `S8FrozenRow.row_step_total`; new `OraclePortJoinSplitS8.row_total` packages its **same** iterator/read/range/canonical/cadence hypotheses into `RowArgs`; inherited all-prefix/reducer algebra | Whole Vec/iterator/strict-scan body, final flush, concrete finish/caller writes and source pin. A typed local invariant is **not** all-storage totality. **S8 owner** |
| S9 | `J(.s9)`: factored S2 Libra low/high powers and weight loops, full machine state | `AspisR1.S3S9CurrentSourceModel.old_s9_weight_eq_factored`, `s9_source_weights_equal`; `S2LibraFactoredIdentity.source_scaled_eq` are algebraic identities | Current checked factored machine/loops and operand/caller totality, adopted source pin. **Session A** |
| S10 | `∀ i, Covered inventory (tree i)` (`S10Join`), with each `Site` recording exact declaration and owner | Existing inventory audits; no inventory membership theorem proves execution. New core checks all value continuations, including rejection paths | Instantiate the **current** admitted declaration list, reconcile 29 retained unresolved declarations and production `candidate::query_values` owners, all opaque callbacks, generated-name collisions and exact source/toolchain hashes. **Session A** |
| Parser/compact codec | `J(.parserCodec)`: full source `parse_shape`/canonical scan/semantic rows/strict codecs and stored→reached projection; exact Option/Err result for every byte slice | `OraclePortStoredParserC4.parsed`, `parse_of_parts`; `OraclePortCompactDraft` defines exact model offsets/row framing; S2 header and fixed-field parser are local total facts | Whole frozen scanner/row parser/compact expansion equality, all offsets/length/canonical guards, binding D by construction; parser/S2/S8 owners |
| Multiproof | `J(.multiproof)`: `batch_tree`/`verify_in_place`, sorted keys, duplicates, padding, idx/val mutation, node consumption and **ordered reads on failure** | `OraclePortBatchDraft.execute_trace`, `retained_consistent`, `slot_root`; R13 sort/support/dedup-step and inner-level fold results | Whole dedup scan, 18-level parent/sibling simulation, zero-scan backend, source accepted-tx2/read coverage; **R13/S7 owners**. Eager-vs-short-circuit obstruction below belongs to composition |
| Checkpoint ABI | `J(.checkpointAbi)`: 1768-byte encoding/resume, exact prepared/accumulator fields, three digest operations and error timing | `OraclePortCheckpointAbiC5.encode_length`, block widths/offsets and codec roundtrip lemmas; C5 prepared/slices/resume model compositions | Frozen writer/resume→byte model, digest order, stored/public/proof and state provenance, source adoption. **R15/checkpoint + adapter owners**; runtime sameness is still P2′ |
| Pool caller / ASQ8 | `J(.poolCaller)`: exact CPI program/accounts/payload, hint strip, public reconstruction and both variants; preserve ordinary error results | Six retained ASQ8 Kani roots include full Result `shipped_pipeline_normalization_equivalence`; `ASQ8Normalization.success_bytes`; `ASQ8PoolHandoff.handoff_bytes`. New `OraclePortJoinSplitASQ8.pool_handoff` consumes that exact P6 normalization contract and the extracted strip | CPI/AccountInfo/PDA/ownership guards, proof/checkpoint/public same-snapshot and transaction order; **Pool/runtime owner**, P2/P2′. ASQ8 is 320 bytes; reconstructed ASF8 is 1880 bytes |

The local adapter modules instantiate available **local** facts; none supplies
an entire `PerConeJoins` field. In particular, the S7/S8 typed records expose
upstream hypotheses rather than eliminate them. Their arguments must be
constructed from all raw caller inputs after ordinary error-producing guards.
Returning outer `ok (Rust.Err e)` is compatible with total refinement;
assuming outer `ok` to prove outer `ok` is not.

### R17 and R22 integration

`OraclePortJoinSplitR17.lookup_join` applies the landed symbolic table theorem
to `TableJoin a b`, whose exact two fields are:

```lean
A : ∀ i, i < 512 → a i = tableA i
B : ∀ i, i < 512 → b i = tableB i
```

The optimized R17 certificate checks all 512 entries of each literal table
and all source indices/line coordinates. It is executable P6 evidence,
not a kernel proof of these two equalities for an arbitrary supplied array.
`model_lookup` instantiates them for the model tables. Dynamic inverse/prefix
vectors are **not** embedded tables; their construction remains S7.

`OraclePortJoinSplitR22.total_join_R22` instantiates the existing general
`R22TotalCheckedComposition.total_refinement_R22`: total outer-success
refinement **plus** `Translation source` gives `NoOverflow` and identical
wrapping results for each input. The S5 reducer/multiply operational proof
already supplies that translation locally. Fixed parser/sampler, row/inactive,
layout and stage-2 constants have the exact R22 corollaries catalogued in
`R22-TOTAL-20261021.md`. Accepted-only power/tower/dot/residue facts still
need independently established caller domains. Totality does not identify
source pins, widths, casts, opaque callees or the native SBF artifact by itself.

### Ordering obstruction: child success equations are insufficient

The read-only frozen caller `candidate.rs:166–168` calls its three
`batch_tree` children using `?`. A failing tree immediately returns; later
trees are not run. `OraclePortBatchDraft.verifySlots` instead binds the
head, unconditionally binds the entire tail, and only then returns
`ok && tail`. It is an **eager** conjunction. The difference is visible to
the oracle-program join even if both callers return false.

`OraclePortJoinSplitOrdering.rejected_read_counterexample` proves that an
eager false child followed by one oracle read is not the corresponding
short-circuit program, for every address and oracle world.
`verifySlots_rejecting_suffix` proves the exact conditional obstruction for
the existing `verifySlots`: if its first slot rejects and its suffix performs
at least one read in a world H, it cannot equal the short-circuit composition
of those **same** child programs.

This is not a proved concrete counterexample to the full frozen `ExecutionJoin`:
it does not construct a stored proof satisfying every upstream guard or
identify its complete frozen execution with those children. It proves that
local child refinements alone do not establish the required ordering join.
The source additionally hashes sorted leaves (including duplicates) before
entering the level-by-level `verify_in_place` loop, whereas the model's
recursive tree execution and retained duplicate checks have their own order.
That order also needs explicit simulation; equal Merkle roots are insufficient.

**Owner / next step:** the oracle-port composition owner with R13/S7 must
either supply exact source/model trace simulation (including early errors,
duplicate placement and checkpoint reads), or propose a new source-shaped
decision and redo its probability/cost consumer. Existing modules cannot be
edited by this worker, and the unmerged port needs user approval. This packet
does not change dV or assert this residual is discharged by Session A's
arithmetic re-pins. Raw source/function hashes and the compared bodies are
pinned in `ordering-source-pins.json`.

## Release boundary

`OraclePortJoinSplitHeadline.final_soundness` is a distinctly named sibling
endpoint consuming `executionJoin_of_cones`; `per_query` retains exactly
the draft's numeric bound and domain `32 ≤ Q ≤ Qmax`. No M10 definition,
cost, scan allowance or probability constant changes.

The controlled before/after pair is
`final_soundness_with_execution` / `final_soundness`. The before-signature
**already contains every split premise**. Normalizing only the theorem name,
`delete-redundant-execution.diff` removes exactly this line:

```lean
    (h_Rust_equals_dV : ExecutionJoin D rust)
```

`split-before.lean.txt`, `split-after.lean.txt` and
`deleted-premise-verbatim.lean.txt` preserve the exact signatures/premise.
This establishes redundancy **under the complete split**. Replacing the
original C7 execution premise by the split is a conditional factorization,
not an advertised strictly weaker or unconditional source theorem. No
original endpoint premise is claimed discharged: R19, C7 and the execution/
stored-binding definitions remain byte-identical to `3a01b2d6d`.

Reproduce the signature check without Lean or a solver:

```sh
python3 -B tools/oracle-port-join-split/signatures.py
```

`StoredCarrierBinding D rust P runtime` is independent of the execution split
and remains exactly as in C7. Total program equality alone does not establish
checked arithmetic safety: R22 additionally requires outer Aeneas success
and the operational P6 `Translation` (or the precise Kani harness domain).
Focused cached-object checks are not a coherent frozen release replay.
