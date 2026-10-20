# Builder refinement — 2026-10-21

Branch `codex/cx-builder-ref-20261021`, base `9ba738457`.

## Scope and status

**Partial closure; the deployed obligation remains OPEN.** All four builder
fields are proved for the canonical extracted composition on embedded
Rspend⁺ instances. The shipped compile entry points do not yet have the
source-identification certificate. Pinned Aeneas rejects their validation
loop; this item stops at that translation blocker, as permitted by the task.
No prover, verifier, on-chain source, or existing Lean module was changed.

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

## Exactly what remains

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
