# Prover commitment continuation 12 — 2026-10-21

Branch `codex/cx-prover-commit12-20261021`, base `3ac016af1`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit12-20261021/`.

## Scope and stage ledger

The 600-second whole-scalar check is not rerun. The replacement checks one
shipped loop iteration with verified next-word contracts and proves the
extracted loop schedule separately by Lean induction. No source join is
assumed discharged by a local helper theorem.

The headline remains unchanged pending evidence sufficient for deletion.
Peer-owned SourceIdentification, RustRuntimeJoin and PrivacyR1FinalRelease
files are excluded from this work.

## Stage 1: split scalar call sites and finite schedules

`state_only_hiding::callsite12::mask_iteration` and
`state_only_entropy::callsite12::source_iteration` are generated from the
literal shipped scalar loop bodies. Each uses the verified contracts of
its actual `next_word` and the reference `next`; each compares the scalar
result and all four retained state fields. The local nine-answer table
covers one iteration only and is shared between the compared sides.
`mask-iteration-v4` passes (10.361 s, 660620 KiB parent peak RSS, zero swaps);
`source-iteration-v1` passes (11.459 s, 660408 KiB, zero swaps). The receipts
also record the authoritative cgroup peak and 6G/8G/no-swap/64-task limits.
The expected work is Kani compilation and bounded verification, not native
arithmetic. These are new one-iteration targets, not reruns of the timed-out
scalar contract. All 550 Rust/Cargo inputs in the host snapshot match this
revision or the literal appended proof-only sources, as checked by hash.

`ProverCommitShippedSchedule` abstracts the next-word call in the retained
extracted scalar loop schedules. `mask.scalar_sixteen` and
`source.scalar_sixteen` prove by induction that precisely sixteen tries are
available, success returns immediately, rejection retains the evolving
state, and exhaustion uses the state after the last try. The mask iterator
is `Usize`; the source iterator is `I32`. J8359 passes all six new theorem
audits with only the standard three axioms: 2.02 s, 2578880 KiB peak RSS,
zero swaps. The literal generated source and generation input hashes are
retained. This is a proof-cut schedule; it is not an assertion of a complete
Rust entry-point refinement.

### Rejected direct-extraction route

J8356 is an excluded elaboration draft. More seriously, inspecting its
axiom output exposed `Aeneas.Std.core.fmt.Formatter` in the actual extracted
next-word methods (via slice-conversion `unwrap`). J8357 is a diagnostic
only, with no theorem: all four actual extracted methods (`next_word` and
`m31`, both streams) have that forbidden dependency. It exits 0 in 1.20 s,
2539656 KiB peak RSS, zero swaps; passing compilation does not make the
axioms acceptable. The generated proof-cut schedule deliberately abstracts
the callee; it does not silently adopt the tainted direct-extraction theorem.
J8358 is an excluded unsigned-iterator arithmetic draft, fixed in J8359.

The first two Kani launches fail before verification because a referenced
builder-tree source is absent (a failed upload initially left it absent).
The third uses an incomplete exact harness name. The complete source graph
and fully qualified name are fixed before the accepted fourth launch.
No failed proof or memory-pressure result is rerun unchanged.

No production Rust/Cargo source is edited. The host snapshot was cloned by
hard link; the four replaced proof sources were installed by atomic rename,
so the predecessor workspace and its cache were not modified. Only this
worker's new Lean modules are installed in Env J; overwritten own drafts
and objects are snapshotted by the launcher. No peer-owned file is changed.

## Stage 2: state transport and a concrete deletion obstruction

`ProverCommitShippedTransport.finite_transport` composes a next-word step law
between distinct state carriers through any number of remaining tries. Both
scalar transport theorems apply it to the fixed sixteen-try schedules,
retaining success, exhaustion, operational failure/divergence and the exact
mapped final state. The step law is an explicit hypothesis, not a concrete
Rust instance smuggled in by the theorem name. J8362 passes all four axiom
audits: exit 0, 1.44 s, 2560240 KiB peak RSS, zero swaps. J8361 is an excluded
elaboration draft, replaced after reducing the pure bit-mask lift.

`ProverCommitBuilderDeletionObstruction` establishes an actual counterexample
to a blanket deletion of `builder_premises` at the current endpoint.
`badInput pub` has a `Unit` witness, returns exactly `pub`, and puts the
concrete tower element `PrivacyR1AcctBasis.i` in every trace cell.
`i_not_base` proves that element lies outside the headline's base subfield.
`builder_premise_false` proves the builder premise is false for this input,
even after `PhaseWireLog2Bin.honest` fixes the transport. Consequently
`no_universal_builder_discharge` proves there is no theorem supplying the
builder premise for every permitted `input`, for any public statement and
handle. J8360 passes the three axiom audits: exit 0, 2.31 s, 4112556 KiB peak
RSS, zero swaps, standard three axioms only.

This does not refute the concrete Rust builder. It identifies the missing
input/source identification: the top theorem still quantifies over an
unconstrained build function. Per-call scalar or hash-frame facts do not
constrain that function. Specializing `input` would change the quantifiers;
it is not the requested deletion-only change. No peer-owned identification
or runtime-join file is modified.

## Stage 3: transcript and binary-node callback checks

The new callback observers check the actual generic `Digest32` methods'
framing, call count, returned answer and retained state. Payload forwarding
is checked by exact slice pointer and length, so arbitrary payload bytes are
preserved rather than replaced with a fixture. Responses are arbitrary
traces; they are not assumed fresh independent ROM samples. Proving framing
for that larger class also covers consistent deterministic oracle traces,
but supplies no probability law or complete adaptive execution coupling.

Accepted checks cover outer transcript `new` (S2), `absorb` and `block`;
semantic transcript `new` and `sample_block_validated`, including wrong-row
rejection with no calls and unchanged state; and binary parent hashing
`0x12 || left || right`. Explicit bounds are payload length <= 2048 and
row <= 32 for the outer transcript, framed length <= 3717 and row <= 26 for
the semantic block, and public-byte length <= 4096 for semantic initialization.
The concrete caller must still instantiate these bounds and argument images.

The byte-ROM used by earlier local proofs is not an all-family backend:
`semantic-row25-capacity-v1` checks the actual `row_shape(25)`: payload 3712,
framed record 3717, complete hash input 3751 bytes, exceeding its 514-byte
capacity. The outer row-31 frame can also reach 2086 bytes. The new observers
do not raise that ROM's capacity or silently use it for these calls.

`transcript-queries-prefix-v1` checks the literal source prefix ending just
before `queries_from_pairs`: one absorb followed by eight squeeze/advance
pairs, all on the expected state; both answer buffers, absorbed state and
last advance are checked. `query-prefix.json` pins the exact source fragment.
This is a source-cut prefix, not a full query-method equivalence certificate.
The whole-query comparison executes the sampler twice and was stopped after
263.988 s at a review point (6380792 KiB GNU-time peak RSS; no memory cap
increase). The exact own-process stop and cgroup peak are retained. It is
excluded, not timed out, not a counterexample and not an accepted certificate.
Its replacement proves the prefix without expanding the sampler.

The first semantic initialization trial fails an unwinding check because
its domain exceeds the initial 34-byte comparison bound. Only that harness's
literal bound changes to 84 in the accepted replacement. All unwinding and
safety assertions remain enabled. No scalar-contract timeout is rerun.

| Accepted target | Exit | Wall (s) | GNU peak RSS (KiB) | Cgroup peak (bytes) | Swaps |
|---|---:|---:|---:|---:|---:|
| `transcript-new-v1` | 0 | 2.193 | 345540 | 293654528 | 0 |
| `transcript-absorb-v1` | 0 | 6.836 | 474636 | 555020288 | 0 |
| `transcript-block-v1` | 0 | 3.838 | 379680 | 329170944 | 0 |
| `semantic-new-v2` | 0 | 2.718 | 331588 | 297054208 | 0 |
| `semantic-block-v1` | 0 | 4.463 | 388660 | 338833408 | 0 |
| `semantic-row25-capacity-v1` | 0 | 1.908 | 326612 | 274354176 | 0 |
| `binary-parent-v1` | 0 | 2.332 | 345408 | 294027264 | 0 |
| `transcript-queries-prefix-v1` | 0 | 13.773 | 482088 | 514879488 | 0 |

Every target's exact harness, command, source hashes, resource scope and
full output are in the receipts. Source revision is the pinned baseline
`3ac016af1` with the literal additive proof-only sources; `final-source-inputs.json`
pins the entire 550-input Rust/Cargo snapshot. Every input resolves to that
baseline or an exact retained proof-only candidate. `harness/validate.py`
checks these identities, resource limits, swaps, link flags, active verified
scalar stubs and accepted Lean axioms. No full Rust regression was needed
for these proof-only changes.

`callback-coverage.json` inventories eighteen families with source anchors,
hashes, verified local references where available, and remaining obligations.
It explicitly leaves public digest/outer binding, the inline intermediate
source and D seeds, concrete material/D/salt/packing/tree schedules,
full query result-state transport, and retry/abort histories open. A local
framing check is not promoted to an all-family or whole-shipped certificate.
