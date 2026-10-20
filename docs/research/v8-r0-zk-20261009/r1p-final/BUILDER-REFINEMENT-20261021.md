# Builder refinement — 2026-10-21

Initial branch `codex/cx-builder-ref-20261021`, base `9ba738457`.
D83 continuation checkout: `codex/cx-builder-ref2-20261021`, starting
from the previous worker result `5b1a6582b`. No push or merge.

## Scope and status

**Partial closure; the deployed obligation remains OPEN.** All four builder
fields are proved for the canonical extracted composition on embedded
Rspend⁺ instances. The shipped compile entry points do not yet have the
source-identification certificate. D83's continuation removes the outer-loop
break shape and advances the source work; the full compiler now reaches a
separate borrow blocker in `records`. Continuation 3 now supplies extracted
owned references and decomposed, passing Kani equality gates for records and
the optimized Poseidon external layer. The complete caller/public/glue source
identification is still open.

The continuation's exact results and gates are recorded below. Sections
Stage 1 through the original stop reason describe the previous run; their
statement that no prover source changed applies only to that run.

## Evidence

Focused env-J attempts use only 8400–8599 and are appended to
`attempts.jsonl` by `builder-build.py`. Existing shared sources/objects are
snapshotted before replacement under the branch name.

## Stage 1: extracted composition

`R1Z.BuilderRefinement` defines `mergedTrace` as the word-lift of
`copyCellMerged`. Its prover's `build` is this trace, not the abstract
`buildModelSpec`. `mergedTrace_eq_model` applies `builder_witness_merged`
extensionally. `sound_merged` and `builderSoundOn` supply baseTyped, lanes,
helperSum and helperInactive via D51 and D43/D42.4.

The theorem is explicitly on `Admitted` inputs (`PubCorr`, `WitnessOk`,
`ModelRel`); deriving these from a successful shipped compile is not proved
in stage 1. The transport is still an explicit parameter.

Env J was missing the model-completeness objects. Attempts 8401–8413
compiled the unchanged prerequisite modules, in dependency order; attempt
8414 compiled the new module (exit 0, 3.26 s, 3,991,752 KiB RSS, 0 swaps).
All axiom audits use only propext, Classical.choice and Quot.sound. The
136-link generator `--check` passed before compiling its chunks.
Attempt 8400 failed on a missing HelperInactive object; it was retried
only after both missing helper dependencies were compiled (new fingerprint).
The host snapshots retain any pre-existing source/object before upload.

## Stage 2: semantic endpoints

`R1Z.BuilderSemanticBridge` proves the block endpoint, owner, nullifier,
three-chunk note, input, recipient, change, node and arbitrary membership
prefix identities against R0P.Semantics. The node proof accounts for the
M31 addition/subtraction tweak. No concrete Poseidon evaluation is used.
Attempt 8438 passes (4.48 s, 3,262,736 KiB, 0 swaps), with all thirteen
theorems axiom-audited. Earlier failed sources (8415, 8416, 8421, 8431)
are retained in attempts.jsonl; the initial whnf timeout was replaced by
explicit state/input projection lemmas and local irreducibility, not a limit
increase.

The canonical spend-relation source closure was absent from env J. It was
compiled from the current repository's canonical lean/ files, using the
existing R1-prefixed module names where their imports require them. The
build receipts record `repo_source` for each promoted alias. The first
AppendPair attempt (8422) exposed the missing V7PairLeafOccupancy object;
8424 builds it and 8425 is the dependent retry with changed inputs.

## Stage 3: Rspend⁺ to ModelRel

`R1Z.BuilderSpendRelation.modelWitness` maps every field of the existing
`AspisR1.SpendRelation.Witness`. `RspendPlus` is exactly Rspend plus D50's
transfer change sentinel. `modelRel_of_spend` derives all semantic ModelRel
fields: auxiliary occupancy/conservation/amount, public digest identities,
append root/carry, and PairRight. It takes only public/witness base-field
membership in addition to Rspend⁺. PairRight is derived from the selected
commitment and first sibling, not assumed.

Attempt 8443 passes (2.12 s, 3,522,140 KiB, 0 swaps), all six theorems use
standard axioms. Failed attempts 8441/8442 were corrected proof sources;
no resource limit changed. This closes T4's semantic relation implication,
but does not yet connect the shipped records function to this witness map.

## Stage 4: canonical inputs and the four fields

`R1Z.BuilderCanonical` defines the canonical RustWitness/RustPublic maps
from M31 public inputs and Wspend, and proves their lifted merged trace
equals the model on the embedded semantic witness. All public/witness
base-membership facts are derived: any subfield contains the image of the
prime field. Its honest instance is a subtype carrying only Rspend⁺ on the
embedded witness and public input, with no ModelRel or trace-validity field.
`builderSoundOn` supplies all four fields for this concrete extracted
builder. Attempt 8444 passes (2.35 s, 4,005,424 KiB, 0 swaps); all seven
theorems have standard axiom audits.

This still is not a theorem that the shipped compiler's successful input
projects to this subtype, or that its Rust structural glue is the extracted
Lean composition. Those are the next source obligations.

## Stage 5: fixed transport and source handoff

`R1Z.BuilderSource.prover` fixes π to `AspisR1.rowEquiv`, D18's involution.
The `coefficients` theorem checks the orientation: `coeffsOf π t c j` is
`t c (row j)`, as in S2's `Variant::coefficients`. `rows_coefficients`
restores the original rows. These are mathematical transport facts; this
module does not claim extraction of `Variant::row`'s Rust bitwise loop.

`BuilderSource.builderSoundOn` closes all four fields for this fixed
mathematical h, public map, relation and extracted build. The separate
`SourceIdentification source toInstance` has exactly public_eq, build_eq,
and transport_eq. Its `toInstance` codomain requires membership in embedded
Rspend⁺. `builder_refinement_D46_D51` transports all four fields along such
a certificate. **The certificate is not constructed for shipped Rust.**

Attempt 8445 compiles unchanged D18Transport; 8446 compiles the new root
(exit 0, 2.47 s, 4,000,548 KiB, 0 swaps). The final five extension modules
have 39 theorems; `builder-audit.py` checks each axiom line, final source SHA,
and current direct-import object fingerprint. `builder-audit.json` records
the exact commands, revisions, object SHA/size and caps. No existing privacy
root changes, so none is rerun; no full frozen-manifest replay is claimed.

## Shipped path identified by source inspection

All paths below are repository-relative. This table is source inspection,
not a replacement for the missing `SourceIdentification` proof.

| Component | Shipped source and correspondence |
|---|---|
| Honest domain | Successful `compile_pool_v1_pair_forest_{private_transfer,withdrawal}_merged_c1_v1` in `crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:369,421`. Its admission checks additionally constrain positive values, context, pool/domain, snapshot binding, pair selection, canonical words, roots and output digests. Rspend⁺ is the semantic privacy relation, not a claim that these admission checks are equivalent to the whole relation. |
| Raw witness | `pair_forest_copy_builder.rs:227` (`records`): values; key/salt; selected pair bit and other commitment at level 0; membership index bits/siblings at levels 1–20; super-root bits/siblings at 21–23; pair coordinates/inverse; output owner/salts. Withdrawal uses zero recipient owner/salt. The canonical Wspend projection must reflect that choice. |
| Public semantic map | `pair_forest_semantic_terminal.rs:1327–1361`: anchor/nullifier/asset/change from the transaction; Some recipient and no amount for transfer; no recipient and Some amount for withdrawal. `nextPairIndex` and snapshot frontier come from `compiled.public_statement.live_snapshot`; nextRoot and nextFrontier from its candidate_afterstate (`pair_forest_trace.rs:347–352`). Pool/domain and other byte-level context remain outside R0P.Public and must be retained by the outer wire mapping. |
| Builder | `compile_forest_from_copies` creates CopyRecords, checks digests/admission, obtains `records.banks()`, validates Poseidon rows, and returns merged bank columns as `semantic_c1`. The noised trace and random mask/helper columns are later supplied by `prover.rs`/`host_semantic::build_with_material`; the h.build here is the unmasked trace, with columns 16–28 zero. This does not prove the later masking/refusal path. |
| π | S2 is required by the binary prover (`crates/aspis-r1-cost-probe/src/prover.rs:205,302,356`). `transport.rs:4–21` uses TAU=[3,4,2,0,1] and coefficients[j]=rows[row(j)], the D18 arithmetic permutation instantiated above. |

The standing `check-glue-text.py.txt` and `gen-glue.py.txt --check` both pass
on this revision. They verify pinned copies, 30 verbatim structural glue
functions, bank-merge lines and the shared generated table. They remain
text/generator evidence, not a Lean theorem about the complete Rust caller.
The prior D70 differential suites were not rerun: their sources are unchanged.

## Actual extraction attempt and stop reason

`builder-extract.sh` runs the two shipped compile entry points, with the
pinned r18 kit, in a separate MemoryHigh=6G / MemoryMax=8G /
MemorySwapMax=0 / TasksMax=64 scope, release profile, four cargo jobs.
The workspace contains byte-identical Rust sources (170 source pins verified
against this worktree) and only narrows workspace membership. The first
resolution attempt lacked Cargo.lock and failed on the yanked spin 0.12.1
transitive dev dependency. Supplying this revision's Cargo.lock resolved it;
that failure and the changed environment are recorded, not discarded.
Two initial reservation preflights declined launch while +8 GiB would exceed
the 55 GiB host allowance. No other job was stopped.

Charon succeeds: has_errors=false, exit 0, 16.85 s, peak 614,524 KiB,
0 swaps. LLBC SHA256 is
`f7324890645069fed416506943f37c5b490927f7b2188b93110ea10f7c7d1a9b`,
size 7,258,347 bytes, retained on host only. Aeneas fails: exit 2, 0.45 s,
133,056 KiB, 0 swaps:

> Breaks to outer loops are not supported yet

It names `pair_forest_trace.rs:158–197` (`validate_forest_poseidon_rows`)
and `PrePasses.ml:648`. This is a translation blocker, not a memory failure.
No unchanged larger-cap retry, prover rewrite, or Kani equivalence claim was
made. The task explicitly permits stopping and reporting at a translation
blocker. A later reference/equivalence route would need Kani's fixed admitted
sizes and a named P6 soundness premise under the prep5 ruling.

`builder-extraction.json` contains full logs, exact targets, source/tool pins,
source revision and time receipts. Charon tool SHA is `daad69be…336af8`;
Aeneas is `959659a6…709e3`. No binary or LLBC is committed.

## What remained after the first run

1. Construct a source instance map from successful shipped compiler inputs
   and outputs into `BuilderCanonical.Instance`: prove the semantic public
   projection and embedded Rspend⁺, including admission/value ranges and the
   withdrawal recipient-zero convention. The equivalence between the
   relation evaluated in M31 and its embedded K form is not separately proved.
2. Prove that shipped `records` equals the canonical Rust record map, and
   that the complete Rust structural glue/banks yield the Lean merged trace.
   D70 migration, generated text and prior differential tests are evidence;
   they do not discharge build_eq in Lean.
3. Prove the Rust S2 bitwise row loop equals D18 π and assemble the three
   SourceIdentification fields for the actual h. The current transport
   theorems identify the mathematical orientation only.

Until these are supplied, leave the first open row of
PRIVACY-FINAL-20261020.md in place. No other privacy definition-of-done row,
retry/publication coupling, wire identification or final release claim is
closed by this work.


## D83 continuation: validator control flow

The candidate splits validation into row, block, and bank traversal. Row
validation retains early return for the first bad lane. Block/bank traversal
carries the first error in a Result and stops through the while condition.
It preserves block order, local rows, lane order, error payloads, round
schedule failure, and the stable/late bank selection. No writers or copy
arithmetic change. The validator is retained after every required before/after gate passes.

Two distinct extraction failures are retained in
`builder-d83-evidence/continuation.json`: the first early-return split still
failed at PrePasses.ml:648; the Result-carrying form gets past that pass.
Both complete compile entry points were Charon-extracted together, with
has_errors=false. Their Aeneas translation then fails at
`pair_forest_copy_builder.rs:230`, InterpAbs.ml:1688 (selected sibling).
Extracting only the validator reaches `poseidon2.rs:193`,
InterpBorrowsCore.ml:1498 (the existing lazy external-layer iterator).
Neither failure is memory pressure. No larger-cap retry is used.

The fixed-seed S2 transfer and withdrawal proofs and public bytes compare
byte-for-byte. The codec 1,233 trace is byte-identical. Ordered digest calls
compare exactly; the randomized HashMap summary `repeated_exact_inputs`
compares as a multiset, as already specified in D70. The 512-witness glue
suite and the 2-fixture/512-honest/2,046-mutation migration suite pass.
P_R1 accepts and verifies all eight independent attempts, and its retry loop
publishes a proof after one attempt which also verifies. All D83 runtime gates
pass; full receipts are in `builder-d83-evidence/validator-gates.json`.
The ordered trace has 1,095 entries for the adopted frozen fixture.

## D83 continuation: S2 equivalence and Lean reference

`tools/r1-builder-reference` is a standalone test/extraction-only crate.
Its Kani harness includes the actual shipped transport source by path,
with no stubs. Kani 0.67.0 proves, for all usize j < 1024, S2.row(j) equals
D18's arithmetic digit permutation, lies below 1024, and is involutive.
All 78 checks pass (two unreachable), unwind 6 with unwinding assertions.
Kani's default solver is embedded CaDiCaL; the inventoried Kissat binary
was not selected. `transport-kani.json` pins the sources and tools and
records 4.98 seconds / 528,804 KiB / zero swaps. This route depends by name
on P6's Kani/CBMC soundness, rather than adding a Lean postulate.

The arithmetic reference extracts successfully with the pinned kit, and
`R1Z.BuilderTransport.reference_row` proves its extracted machine-word
result equals D18.rowNat, including absence of wrapping. This holds for
all machine words; `reference_row_fin` identifies the admitted Fin 1024
transport. Env-J attempts 8450 (extracted definition) and 8452 (refinement)
pass. Attempt 8451 was a local proof failure corrected by reducing each
monadic bind before rewriting the next operation. Both theorems audit to
propext, Classical.choice, Quot.sound. No proof limit was raised.

The generated Lean definition is unchanged except that import Aeneas is
replaced with the two standard env-J port imports. The raw and adapted
source pins are in `transport-extraction.json`. Focused audit now covers
41 extension theorems. Existing privacy roots were not changed or replayed.

This certifies S2's row-index function through the approved P6 reference
route. It does not construct a source HonestProver or its records/glue/public
relation map. The array wrappers and the actual source h must still be
assembled before claiming its SourceIdentification.transport_eq field.
The SourceIdentification structure and the final privacy theorem therefore
retain their existing conditional statements.

## D83 continuation: records reference route

A Kani-only same-crate harness calls the actual shipped records function
and a reference that copies the input records before branching. It compares
every RustWitness and RustPublic field, without stubbing pair_empty_roots
or the record mapper. The unstubbed job was stopped after 7:49.06 during whole-cone verification, including the fixed
empty-root hashes; the dominant substep was not profiled (SIGTERM, no solver verdict; last sampled CBMC RSS
3,649,508 KiB, true peak not captured). GNU time's stopped-parent RSS/exit
line is not used as a success or whole-job peak. No cap increase or unchanged
solver retry followed.

The replacement harness uses a single shared arbitrary `[Digest; 21]` return
for the identical pure zero-argument `pair_empty_roots` call in both mappers.
This isolates record projection for all possible helper results. Its scope
is explicitly parametric in that result; transporting it to the actual
helper requires the common pure-call congruence argument. It does not prove
the hash implementation, caller admission, or the final SourceIdentification.
Kani requires the named unstable `stubbing` feature for this route; the
initial invocation without that option failed at compilation and is retained.
The changed invocation compiled, and Kani metadata confirms the intended
stub. It was stopped at a MemoryHigh review after 6:08.11, again without a
solver verdict. The last recorded aggregate cgroup peak is 6,547,927,040 bytes
(about 6.10 GiB), swap 0; memory events report no OOM or hard-cap hit.
Its GNU-time parent RSS is incomplete after SIGTERM, so no true process
peak RSS is claimed. The shared-root replacement is also expensive; the
hash computation was not the only cost. Both stopped commands have effective
exit 143, overriding GNU time's misleading stopped-parent `Exit status: 0`.
Neither is a successful equivalence certificate. No unchanged rerun, higher
cap, or fabricated P6 fact is used to close the source obligation.

Both harnesses are absent from ordinary prover and program builds. No
successful whole-compiler reference extraction or Rust glue equality
certificate is claimed.


## Current open obligations after D83 continuation

1. Translate the complete compile entry points or finish the approved reference
   route. The new blockers are the records selected-sibling borrow and the
   optimized Poseidon external-layer borrow, at the locations above. The
   bounded whole-record Kani experiments are not sufficient; isolate per-loop
   or per-field contracts before another large run.
2. Derive the embedded Rspend⁺ instance and semantic public projection from
   successful shipped compilation, including canonical word/value bounds,
   the change sentinel, live snapshot/afterstate fields and withdrawal's
   zero recipient convention. No actual source HonestProver is defined here.
3. Certify the shipped records against the canonical RustWitness/RustPublic
   maps, and prove the Rust structural glue/banks equal the R1Z builder model.
   The unchanged text/generator checks and successful 512-witness gates remain
   measured/textual evidence, not a universal source identification theorem.
4. Assemble the actual source h, its array transport wrappers and all three
   SourceIdentification fields. S2's row-index function now has the named-P6
   Kani/reference plus kernel-refinement evidence. It alone does not supply
   the missing public_eq/build_eq fields or the source instance map.

`builder_refinement_D46_D51` in PrivacyR1Final remains conditional and the
first definition-of-done row stays open. PrivacyR1Final itself is unchanged;
its roots were not recompiled. The two added Lean modules were compiled in
isolation through env J (8450, 8451 failed, 8452 corrected); final audits have
only standard axioms and zero swaps. No complete frozen-manifest replay was
run. All native gates and extractions used capped no-swap host scopes. No
verifier, on-chain source, writer extraction input, wallet or key changed.

Continuation commits: `057c5c5e0` (S2 Kani), `d294bed4b` (S2 extraction and
Lean refinement), `bc2867479` (validator and all required gates); the final
report commit retains the records experiments and exact outstanding boundary.

## Continuation 3, Stage 0: exact-source ELF gate

Rebuilt all three selected SBF programs from revision df54ab57e on the host.
All 258 pinned files across both program roots, all three linked repository
crates (including aspis-statement), Cargo.toml and Cargo.lock match this checkout.
Default verifier, devnet verifier and Pool match every frozen stripped ELF hash
in freeze-20261020/artifacts-sha256.txt exactly. Receipts retain commands, feature
sets, deployment IDs, toolchain path, exit, wall time, RSS, swap, source revision
and no-swap cgroup limits. No source restructuring or D83 runtime rerun was needed.
See builder-d83-evidence/frozen-source-check.json and
builder-cont3-evidence/elf-rebuild.json.

## Continuation 3, Stage 1: bounded reference route

Both borrow frontiers now have owned reference forms that translate to Lean.
The shipped functions remain unchanged. The only shipped-file edits are
cfg(kani)/cfg(aeneas_ref) module declarations appended at EOF; reference bodies
live under tools/r1-builder-reference. They are absent from ordinary builds.

The optimized external layer is decomposed into the four-lane matrix leaf and
the layer's call trace/aggregation. `mat4_owned_equals_shipped` proves the leaf
for every u32 input. `external_owned_call_trace_and_outputs` checks every callee
argument and exact call count, supplies a shared arbitrary result table, and
compares every output. Thus pure-call congruence and the checked leaf compose
the layer equality under the named P6 Kani/CBMC soundness premise. Unwind 5/17
and unwinding assertions are explicit. The older direct full-layer harness
stopped at 120 seconds without a verdict; its replacement is the decomposed
proof, not a larger-cap retry. The mutable reference itself hit an Aeneas nested
loop join blocker; the owned-array replacement translates successfully.

The record reference takes owned inputs and a supplied empty-root table. Aeneas
rejected the first borrowed/copying reference and then its indexed version;
taking the arguments by value removes that borrow frontier. Explicit u32 shift
counts avoid the port's Usize/U32 shift mismatch. The source change is in the
reference, not a hand edit of the generated function. Generated records and
Poseidon modules retain their generated options; adaptations are env-J imports
and a separate records namespace. Env-J 9200 and 9202 compile; 9201 is the
retained shift mismatch. No success is attributed to its error-produced sorry.

Generic nested `array::map` arbitrary-input construction was itself expensive:
whole-record, symbolic-path, static-path and single-caller experiments stopped
without verdict. Replacing those input constructors by straight-line arbitrary
words preserves all inputs and makes the focused gates practical. No memory
cap was raised. Timeout parent RSS is explicitly incomplete; cgroup aggregate
peaks, zero swaps and exit 124 are retained. Some launches were declined at the
55 GiB reservation preflight; none bypassed it.

The final six records projection harnesses all pass. They cover all 15 RW and
5 RP fields (including withdrawal's zero recipient fields), for arbitrary input
words and a shared arbitrary 21-root helper result. The raw-word leaf passes
separately. Combined public-array equality timed out, so frontier and empty-root
projections were split: each passes in under 90 seconds without changing caps.
`records-field-coverage.json` checks that no output field is omitted. These are
bounded universal component equalities, not a test sample and not the deployed
relation or complete compiler theorem.

Final accepted gates, source/tool hashes, generated import/namespace adaptations,
exact commands, metrics and retained failures are indexed by
builder-cont3-evidence/component-summary.json and kani-and-extraction.json.
No production function body changed. No D83 runtime suite or full privacy
manifest was replayed: the ordinary prover behavior is unchanged, and no final
privacy release or full source closure is claimed. The new generated modules
were added to shared env J under worker-owned names; replacements were
snapshotted, and their required dependent proof is compiled on the corrected
records object.

## Continuation 3, Stage 2: reference projections and exact remaining premise

`R1Z.BuilderRecordsFields.fixed_fields` proves that successful evaluation of
the extracted owned mapper preserves the explicit output value, change value
and public asset. It consumes the corrected 9202 extraction. Attempt 9203
compiles in env J (1.39 s, 2,527,912 KiB RSS, zero swaps); its two theorem
audits use only standard axioms. This is an unconditional implication from
successful reference evaluation, not a proof that the deployed compiler
establishes RspendPlus. The generic bind inversion lemma has only propext.

Stage 2 is still partial. No shipped source HonestProver/instance map, complete
records-to-canonical mapping, or Rust glue/bank equality theorem is assembled.
In particular, the codomain of `BuilderSource.SourceIdentification.toInstance`
contains embedded RspendPlus. The component Kani equalities do not prove that
a successful deployed compilation belongs to that subtype. They also do not
supply the complete public projection, build_eq, or array transport wrappers.
Existing canonical-builder soundness and the S2 row theorem remain available;
they do not fill these missing fields automatically.

`PrivacyR1Final.lean` is byte-unchanged. Before and after, its builder premise is
`(builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)`.
It was neither removed nor replaced with the stronger source-identification
hypothesis. No strictly weaker sufficient premise has been proved for the
actual source h, so no privacy-root replay or final-manifest replay is claimed.
The exact before/after source hashes and outstanding typed boundary are in
builder-cont3-evidence/premise-status.json. Causal/phase-model files are untouched.

The canonical-record handoff also owes the meaning of the actual
`pair_empty_roots` result. The shared arbitrary-root Kani argument establishes
projection equality for every possible helper return; it does not identify
that table with the semantic canonical empty roots or prove its hash calls.


## Final ELF continuity recheck after the reference additions

All 258 program-linked source/manifest pins at 9e3edfbaf match the isolated
host snapshot and remain unchanged in 808392111. After waiting for the total
host reservation to fall below the 55 GiB allowance, the final builds ran in
separate 6G/8G/zero-swap/64-task scopes. Default verifier (22.722 s,
446,856 KiB RSS), devnet verifier (2.407 s, 202,672 KiB) and Pool (21.980 s,
429,724 KiB) all exit 0 with zero swaps and match their frozen hashes exactly.
This second rebuild has a source-change justification: the EOF proof-module
additions landed after the first Stage 0 check. No unchanged full native or
Lean regression was repeated. frozen-source-check.json now points to the final
source pins and elf-rebuild-final.json while retaining the initial receipts.
No binaries, keys, or generated objects are committed; nothing was pushed.

## Continuation 4, Stage 1: builder at the constructed protocol

Branch `codex/cx-builder-ref4-20261021`, base `5f877a406`. The new
`BuilderProtocolInstance` proves the canonical extracted builder's four
soundness fields at WideExact, deriving the field-size bound by an injective
prime-field map. `RustBuilderJoin` isolates the remaining raw builder handoff
on the selected public fibre: each source witness on that fibre must have a
canonical admitted instance with identical public value and raw trace. It
requires neither a global source-instance map nor transport equality.
`join_of_identification` proves the old certificate implies this join.
This is a sufficient conditional interface, not an inhabited Rust certificate,
and is not asserted to be logically weaker than BuilderSoundOn itself.

Env J 9204 failed on a missing concrete CharP instance and a notation/parser
collision; 9205 supplies the instance through the injective algebra map and
passes. Only standard axioms occur. Full receipts are appended to
`builder-cont4-evidence/attempts.jsonl`. The private launcher is an exact copy
of run-joint.sh with TasksMax changed from 128 to 64; invoking it with 8 selects
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0. It retains the same reservation,
locks, duplicate-input guard, env J and evidence paths. Shared sources and
objects are snapshotted under this continuation's branch before replacement.
No shipped crate file changes in this stage.

`PrivacyR1FinalProtocolBuilder.privacy_R1_protocol_builder` passes env J
9207 (4.13 s, 4,099,516 KiB RSS, zero swaps). Attempt 9206 retained a
projection-notation elaboration error; parenthesising the notation fixes it,
without raising any proof limit. Its only axioms are propext,
Classical.choice and Quot.sound. The endpoint fixes h to BuilderSource.prover
and removes builder_refinement_D46_D51. It retains hpub and the complete real
and ideal ScanCoupling premises. The real builder/checker/retry row remains
an execution join: builder soundness alone cannot establish its probability,
publication or serialization fields. No concurrent history modules change.

### Verbatim signature before (D89)

The surrounding namespace supplies arbitrary h, base, B, outputs, x and F,
and K=WideExact. All retained binders below have their original quantifiers.

```lean
theorem privacy_R1_protocol
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ScanCoupling
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x))) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454
```

### Verbatim signature after (canonical extracted builder)

Here `h` is local notation for `BuilderSource.prover (K := WideExact)`;
it is no longer an input. This specialization is not source admission.

```lean
theorem privacy_R1_protocol_builder
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : (h).Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : (h).Instance),
      (h).public w = x.1 → ScanCoupling
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 (h).transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling
      (idealTestS source adv x (simE (h).transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 (h).transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (h).transport B outputs x))) :
    ZK_FSS h B outputs source x (simE (h).transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454
```

## Continuation 4, Stage 2: complete raw-record reconstruction and assembly

`BuilderRecordCanonical` proves a lossless round trip for **all fifteen**
RustWitness fields. CanonicalWords lists every required bound: the three
30-bit values, all direction bits, every sibling limb, every key/salt/owner
limb and every pair coordinate. No modular reduction or nonzero-bit alias is
silently accepted. The decoded Wspend retains pairFirst and all withdrawal
recipient coordinates; whether those coordinates are zero is determined by
the source record map, not erased by reconstruction.

`BuilderPublicCanonical.public_roundtrip` recovers all five RustPublic fields
from PubCorr over M31 and canonical asset. In particular the empty table is
recovered word-for-word using the frozen table bounds. This does not infer
PubCorr.empty from the earlier arbitrary-root Kani checks. Attempts 9209
and 9210 pass; 9208 is a retained proof error (List lookup lemma name and a
bit-expression rewriting shape). There is no large numeral or recurrence
reduction, and no new heartbeat/recursion setting.

`BuilderRuntimeJoin` now gives the complete final SourceIdentification
assembly: `toInstance`, both canonical record equalities, public_eq, build_eq
and transport_eq. It takes **one named uninhabited RustRuntimeJoin** with
primitive runtime data/obligations: exact public projection; canonical raw
words; PubCorr including computed empty roots; RspendPlus admission including
the sentinel; raw glue trace equality; S2 transport. It assumes no
BuilderSoundOn, lane, helper or trace-validity conclusion. This factors out
the record reconstruction and final assembly from the genuinely unproved
Rust admission/glue handoff; it does not claim that bundling those obligations
is itself a deployed-source proof. Attempt 9211 passes.

`PrivacyR1FinalProtocolBuilderSource.privacy_R1_protocol_source`, in the same
endpoint file, keeps D89's arbitrary h and consumes this named runtime join
in place of builder_refinement_D46_D51. Its real/ideal ScanCoupling statements
are exactly unchanged. Both endpoint variants compile at 9212 (6.93 s,
4,101,960 KiB RSS, zero swaps); every audit uses only standard axioms.
PrivacyR1Final and PrivacyR1FinalProtocol remain byte-unchanged.

Source-facing signature change, verbatim binder before:

```lean
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
```

Verbatim binder after (every other D89 binder and conclusion is retained):

```lean
    (runtime_join : BuilderRuntimeJoin.RustRuntimeJoin h)
```

This is a source-facing conditional endpoint, **not** a claim that the new
binder is weaker than BuilderSoundOn. The canonical endpoint above has no
builder binder at all. The actual shipped runtime has not yet been made an
inhabitant of either SourceIdentification or RustRuntimeJoin.

## Continuation 4, Stage 3: actual deployed public projection extracted

Directly extracted **the shipped** private_public and withdrawal_public in
pair_forest_semantic_terminal.rs, without any reference or stubs. Charon
passes (20.667 s, 612,152 KiB, zero swaps); Aeneas passes (0.314 s,
68,640 KiB, zero swaps). The raw LLBC/generated pins, exact commands, source
and tool pins and logs are in `builder-cont4-evidence/public-extraction.json`.
The inherited private runner's old revision label is explicitly corrected
there against exact shipped source hashes; it is not source identification.
The env-J adaptation changes only imports and removes the unsupported enum
`discriminant isize` metadata attribute. No enum constructor or function body
is edited; no generated options are added or increased.

`BuilderPublicProjection` proves both complete Public projections and
successful-result implications. These include recipient/amount option shape,
asset, anchor, nullifier, change, live nextPairIndex/frontier and candidate
afterstate root/frontier. Pool/domain and the exact transition remain in
the extracted outer source record. It also derives PublicBase of their
embedded M31 public input. This closes the **projection-function** part of
deployed public mapping, not the successful-compiler admission implication
or identity of a particular source HonestProver.public.

Env J 9215/9217 pass. Retained failures: 9213 missing metadata attribute,
9214 missing predecessor object, 9216 incorrect PublicBase namespace. The
corrected dependency fingerprint justifies the 9217 dependent compile.
All five projection theorems have only standard axioms. No existing privacy
root changes or shipped crate edits are made.
