# Selected owner, input-note and nullifier recovery

2026-09-09. Research branch inspected clean at
`3a0b144dee108041320a23850ab4478444a74745`. This continues the
[24-level selected path bridge](selected-forest-path-review.md), with no
production or existing-proof changes.

## Proved deterministic endpoint and exact scope

[SelectedNoteRecovery.lean](experiments/SelectedNoteRecovery.lean) connects
the selected C1 fields actually read by `recovered_witness.rs::decode` to
the owner, input-note and nullifier hashes in the maintained mathematical
Poseidon model. Its main conclusions, given the explicit individual residuals,
are:

```
trace row11  = ownerHash(decoded key)
trace row59  = noteHash(ownerHash(decoded key), decoded value, asset, decoded salt)
trace row427 = nullifierHash(the same decoded key, the same decoded salt)
```

The decoded key is the concrete eight-limb value at row12, not an assumed
knowledge predicate. The new note equality substitutes directly into the
previous 24-level path theorem, replacing its formerly unclassified starting
digest at row59. The resulting endpoint is the recorded forest digest at
row907; it does not assume that this row is an authenticated public root.

All hash statements use the maintained `gateStep(rc)` and `RoundConstants`
model. This is a **modeled deterministic residual-to-hash bridge**, not an
already-translated theorem about Rust `evaluate_trace_round_pair`, its lazy
M31 kernels or pinned constants. Those source obligations remain explicit.
No valid witness, successful compiler/decoder call, honestly generated trace,
supplied hash equality or supplied round chain is a theorem premise.

## Exact fields, blocks and copying

| Object | Selected C1 cells |
|---|---|
| Nullifier/owner key | row12, columns0–7 |
| Input amount | row44, column0 |
| Input asset | row44, column1 |
| Input salt limbs0–5 | row44, columns2–7 |
| Input salt limbs6–7 | row60, columns0–1 |
| Derived owner digest | block0 final: row11, columns0–7 |
| Input note digest | block3 final: row59, columns0–7 |
| Nullifier digest | block26 final: row427, columns0–7 |

The source's exact active sponge blocks are 0 for the owner, 1–3 for the
input note and 25–26 for the nullifier. Their initial states use domain tags
`0x41530001`, `0x41530003`, `0x41530002` and lengths 8, 18, 16 respectively.
Each block's rate-eight chunk is local row12; local rows0–11 encode eleven
consecutive two-round transitions. Pair zero includes the leading external
linear layer. This matches the mathematical *schedule*, while concrete
implementation/constants equality remains to prove.

The required source copy edges all have weight one:

| Copy | Exact producer → consumer |
|---|---|
| Full note carry1 | row27 columns0–15 → row32 columns0–15 |
| Full note carry2 | row43 columns0–15 → row48 columns0–15 |
| Full nullifier carry | row411 columns0–15 → row416 columns0–15 |
| Owner into note | row11 columns0–7 → row28 columns0–7 |
| Same key into nullifier | row12 columns0–7 → row412 columns0–7 |
| Salt head | row44 columns2–7 → row428 columns0–5 |
| Salt tail | row60 columns0–1 → row428 columns6–7 |

The final note chunk is `[salt6,salt7,0,0,0,0,0,0]`. The six zeros at
**row60 columns2–7 are required schedule constraints**, not the host
inventory's 3,803 relation-free mask cells. The proof requires their literal
vanishing; it does not copy arbitrary padding into a shorter note encoding.

`NoteResiduals` is a sufficient subset containing 1,056 pair-lane equations,
48 initial-state equations, 48 carry equations, 24 key/owner/salt copy
equations and six final-chunk zero equations: **1,182 equations**. It is not
the complete selected residual inventory and does not introduce new verifier
checks. High absorption-lane zeros and all other semantic constraints remain
in the original protocol even where unnecessary for this hash slice.

## Source and proof dependency map

| Source/proof | Actual use and remaining boundary |
|---|---|
| `recovered_witness.rs:44–69` | Literal field read locations and split-salt decoder; canonical shape/limb precheck precedes this model |
| `pair_tree_hiding.rs:105–131` | Sponge carry endpoints and four owner/key/salt copy edge kinds |
| `pair_trace.rs:1059–1088` | Full-state/digest limb layouts, all relevant weights one |
| `pair_forest_trace.rs::build_pool_v1_pair_forest_copy_registry_v1` | Preserves these non-path Poseidon endpoints during auxiliary relocation |
| `pair_forest_semantic_terminal.rs:243–321` | Selected initial-state/domain/length lanes and two-entry final note chunk padding |
| `poseidon2.rs:239–255` | Source round-pair order; concrete model/kernel/constants correspondence remains open |
| `HashMerkleModel.sponge1_forces`, `sponge2_forces`, `sponge3_forces` | Reused deterministic one/two/three-block sponge chaining |
| `V5AcceptedSpendRelation.TwoRoundPermutationRows.toRoundChain` | Reused construction of uncommitted intermediate round states from individual pair residuals |
| `SelectedForestPath.complete_selected_path` | Reused 24-level decoded-sibling path; new note hash replaces its trace-row59 starting digest |

The import closure includes the historical V5 work-normalised ledger, but
the new proof invokes only deterministic algebra/hash-chain declarations.
No old work-normalised bound, grinding assumption or accepted-path capstone
is imported as a security argument.

`exact_public_asset_nullifier` additionally consumes the literal residuals
`row44[1]-publicAsset=0` and `row427[i]-publicNullifier[i]=0`. These occur in
the host public binding family (`pair_constraint_residuals.rs:544–567`) and
the selected semantic terminal (input asset at1165–1168, nullifier digest
alongside row907 root binding). The public parameters are inputs to this
theorem. It does not authenticate them, remove the outer forest-root check,
or replace the caller's spent-nullifier/deployment/account context.

## Remaining payment and soundness obligations

The mathematical field amount is the value of the actual row44 column0.
The earlier selected amount lemma supplies its canonical 30-bit range and
transfer conservation under the corresponding individual residuals. This
hash slice does not assume or prove positivity: `pair_trace.rs:501` still
rejects an input value of zero, and transfer output positivity remains a
separate requirement. No zero-value residual example is promoted to a full
payment forgery.

Other remaining deterministic work includes output-note reconstruction,
combining occupancy/slot validity with the path, canonical byte-to-field
and field-to-u32 source refinement, authentic public root/asset/nullifier
binding, runtime/context checks and atomic settlement. The decoded 20-bit
membership index and three forest directions must retain the actual source
bit ordering. No withdrawal coverage is inferred from this transfer slice.

Upstream, actual accepted execution must still yield authenticated C1
coefficients satisfying these **individual** constraints, with the early
C1 fixing boundary and all replay/resource failures accounted for. Correct
aggregate point claims alone are not that implication. Hash identities do
not make a noncomputable recovered tuple into an efficient extractor.

Privacy and Fiat–Shamir remain independent: no new values are publicized,
and no real witness/key material is printed. This proof does not establish
a full-view simulator, fresh conditional SHA challenges or a resource-bounded
argument of knowledge.

## Execution evidence

The focused leaf passed Lean 4.32.0 with eleven final axiom audits using only
`propext`, `Classical.choice` and `Quot.sound`. The runner checks the pinned
research and read-only main sources, records the imported project-source
closure and cache hashes, and rebuilds no dependencies. All inherited leaf
exports were already present from the preceding continuation.

| Evidence | Exit | Wall | Peak RSS (bytes) | Swap | Outcome |
|---|---:|---:|---:|---:|---|
| [leaf-v1](experiments/selected-note-leaf-v1.log) | 1 | 3.18 s | 5,501,272,064 | 0 | All hash lemmas passed; the single path-start `rfl` failed at differently written digest projections |
| [leaf-v2](experiments/selected-note-leaf-v2.log) | 0 | 3.74 s | 5,646,073,856 | 0 | Pointwise projection simplification closed that goal; complete final axiom audit has no `sorryAx` |

The failed v1 log is retained as failed evidence, not treated as a completed
endpoint. The replacement changes only the proof of equality between the
row59 digest views. No memory/heartbeat limit was raised. Jobs were
serialized with the other agents and guarded by Lean `-M7000` plus an
independent aggregate-child RSS stop at 7,340,032 KiB. Reported wall/RSS
statistics cover the Lean command, not the runner's provenance preflight.

```
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_note_recovery.sh /absolute/NEW.log
```

Pinned mathlib is `81a5d257c8e410db227a6665ed08f64fea08e997`. Final source
SHA256 is
`0c281c1e59a538bc80c9aa88cf8d92f321b140050e9b5e410436696bc7f5a5d3`;
olean
`5fbfa077b05a1d961995621bb763973946ade7b8a10eecaed07b70013c5df33a`;
runner
`cca14fd6e5b8a33d5ff218e547495c15f20f0869322f5060364a3f90da12a0cd`.
`bash -n` and `git diff --check` also passed. There are no active builds from
this task and no commits or main-worktree edits were made by this agent.

No Rust/SBF/proving benchmark or unchanged suite is part of this slice. The
proof body stays **40,282 bytes**; no new proof values, transcript calls or
verifier operations are introduced. Lean time is not verifier CU or
resource-bounded extraction time.

## Decision and next handoff

The extracted input-note digest can now be classified as a note belonging
to the concrete recovered key, and its nullifier uses the same key and salt.
The previous path theorem therefore starts from that note rather than an
unclassified trace digest. This is a real deterministic extension of the
extraction path, while all acceptance/source/resource obligations stay visible.

The strongest next deterministic handoff is the actual selected two-round
source/constant refinement shared by the note and path leaves. One such
bridge would connect all six modeled sponge blocks and all24 path blocks
without adding another honest-fixture-only round trip. In parallel with that
source work, the complete endpoint still needs output commitments, positivity,
occupancy/context and settlement composition; no universal valid-payment
extractor or numerical global security certificate is claimed here.
