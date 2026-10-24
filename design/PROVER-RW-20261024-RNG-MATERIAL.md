# Material acknowledgment and derivation control

Continuation of reviewed dbc123fdc8 and proof 5296e55148. Assigned branch
codex/cx-prover-rw-20261023 only. No shipped source or backend changes.

## Scope and source order

The actual pair-forest producer checks both context fingerprints, obtains
relation-free cells, obtains active rows, and calls build_mask_material_for_layout.
That helper reserves the provided acknowledgment store before rejecting zero
entropy, encoding context, hashing the seed, constructing SeedExpander, finding
an inactive row, and sampling c1, mask-only columns, g and h1 padding in order.
The returned material is constructed from those four replies and context nonce.

The fresh PreReservedNonce acknowledgment is single-use. Layout/cell/active-row
failure occurs before its consumption; zero entropy and later sampling failures
occur after it. The outer durable reservation has already happened before any
of those material-stage failures and is not rolled back by them.

## Validation and boundaries

Work in progress. Evidence lives under rng-material/; old ledgers remain intact.
36 actual Lean launches available at entry (184/220 already used); Kani 44/60.
No full manifest or runtime/ELF/timing gate is authorized or claimed.

Exact cells/active-row source components, first_inactive_row, and the four
sampling components are initially separate unproved source cuts. They are not
primitive instructions. Hash/encoding replies and external type/function holes
remain explicit; no whole-material desired equality premise is permitted.
Physical Drop/clear, getrandom sort/result/destruction transport, old cap8 native
body/audit installation, successful byte/context-to-Raw, and L1/L2 remain open.
E1 is unchanged: ProverCommitPublicNonce40.E1. No probability law is added.

## Established material boundary (stage e9e2ffa9c4)

Control, Paths, Producer, Invariant, Preflight, Finish and Reservation compiled
in focused capped host attempts 11528–11535 (11530 was an elaboration failure;
11531 corrected dependent match elaboration without changing the claim).
`material_success_ack` proves that every admitted material success carries
exactly usedAck and the context nonce, for arbitrary LocalLeaves. No success
result can reach the consumer's missing-ack rejection. `layout_post` preserves
the exact advanced nonce-store value on every admitted helper return, including
all four sampler failure paths; it assumes neither totality nor a sampling law.
`reserve_sample_success` constructs returned reserved secrets and material from
exact hash, encoding, wrapper, clear-call and four ordered sampler replies.
`selected_zero_entropy` and `selected_sampling_failure` compose the actual S2
entrypoint through serialization/binding and reserve into fatal Semantic or
retryable Rejected with the advanced durable-store carrier.

Before: NativeBuildPaths.material_error and missing_ack retained a whole
`buildMaterial ... = ok (status,ack)` leaf premise. After: the concrete selected
failure and reserve_sample_success statements retain only named cells/active
layout components, first-inactive-row, entropy access/equality, exact hash and
four sampler replies as needed. Material construction, acknowledgment
consumption and returned-store control are derived. The intermediate consumer
lemma still accepts the producer result to compose the stages; it is not the
final producer claim. Quantifiers are over the new emitted source carriers,
not the old prototype Body, and there is no native runtime installation claim.

The source cuts are satisfiable local replies, not whole-output contracts:
for example sample_mask_cells may return Err MaskSampleExhausted with a named
advanced expander; successful samplers return field vectors/columns, and the
emitted producer itself inserts the context nonce and assembles the material.
No hypothesis asserts that a material/body result equals a desired security
conclusion. Such reply interpretations do not prove the actual sampler's
arithmetic or install external native sorts.

## Actual caller continuation

The concrete retry_attempt/prove_masked_retrying_with source directly calls
prove_masked_attempt with a borrowed DurableStateOnlyMaskNonceStore and returns
MaskedFixtureAudit. Its callback is FnMut(usize)->Result<actual Secrets,Error>.
This differs from the old prototype's owned-store Body callback returning
(Vec<u8>,u64), and from the prototype's explicit return of the body/policy.
Extracting this caller can prove its local state threading directly without
claiming that the old owned callback has been instantiated. The secure entropy
factory and getrandom transport remain a separate, uninstalled dependency.

## Concrete borrowed cap8 caller

Extraction003/Aeneas002 append the actual retry_attempt, cap8 constant,
prove_masked_retrying_with, Variant equality and RetriedProof (with native
MaskedFixtureAudit). Every preexisting emitted body is textually unchanged.
The 16 external type parameters and 41 local function/component interfaces are
unchanged. The same nonrecursive trait-default expansion used for QM31 is
applied to Variant, and Variant's generated discriminant is retained for its
equality consumer. No backend, shipped code or selected build feature changes.
ct-host-prover already enables r1p-check in the original extraction.

Before rewriting these new job-owned sources/objects in shared J, all were
snapshotted under rng-material/codex-cx-prover-rw-20261023-before-caller; source
copies and object hashes are retained here, objects only on the build host.
11536–11545 replay the changed dependency closure, rather than reuse stale
objects. Only this job's ProverRwRngMaterial modules were overwritten.

Caller.selected_sampling_retry composes the actual emitted body (using the
actual acknowledgment/seed/material source proof) with the actual cap8 caller.
On MaskSampleExhausted it passes the returned durable store and advanced
callback state to the exact recursive call. Caller.selected_zero_fatal aborts
with Semantic and that advanced store. Callback errors return before body
execution, even if the callback error is itself Rejected. The cap branch runs
before the callback. No arbitrary owned Body instance or u64 audit is used.
LastAttempt.last_sampling_exhausted proves the actual sampler exhaustion on
attempt index7 returns AttemptsExhausted with the advanced reserved store.
It uses the existing symbolic Usize value/modulus theorem, not concrete
platform-width reduction; two failed small wrapping-add proofs are retained.

Caller.body_success is **only** the structural consumer of an assumed actual
body success; it preserves the exact native audit, but successful full body
execution is not established. The actual secure entropy factory callback is
not extracted/installed here. Generic callback state is threaded into retries;
the source consumes the callback on a final return, so this theorem does not
invent a returned provider state or prove external borrowed-provider transport.
The former owned FnMut Body prototype remains uninstantiated.

## Remaining producer and actual blocker

The pinned getrandom NonZeroI32 sort/result/destruction transport is still
missing, as established by retained native extraction failure evidence. The
current native source control extraction does not install it, and map_err
error erasure does not supply it. No unchanged niche-failure replay ran.
The next producer is a justified transport for the actual secure callback,
then success-side material application/zero-factor/salts/audit/semantics and
successful bytes/context-to-Raw with ordered events. The four sampler and
layout source components still require their own arithmetic/control proofs;
filesystem reserve_fallible is a component cut, not a proved storage primitive.
Physical cleanup, full cap8 draw inventory, L1/L2, and both deployed targets
remain unestablished. No freshness, retry-uniformity, independent coins,
probability association, new trust, ELF, runtime, performance or adoption gate.
Current ELF pins and later H5/quiet-host gates remain those in the manager
packet; older evidence is not a new identity gate.

## Final focused evidence

Proof source revision c88daf1e50bec23f1d1425b33a4820ce963ddc7d is audited by
11550, R1Z/ProverRwRngMaterialAudit: exit0, wall1.42s, peak RSS2,631,356KiB,
swap0. All38 full theorem signatures/axiom reports are standard only (one
requires no axioms). Complete TypeLeaves/LocalLeaves, material/expander/ack,
nonce-store, audit, status carrier and actual body/caller definitions are printed.
The receipt retains the exact target/command, source/dependency hashes and
revision; summary.json validates all13 current sources against final green
receipts and every recorded dependency object against the read-only current
hash inventory. Imported cached Aeneas evidence is reused, not a full manifest
or coherent release rebuild claim. The expanded caller extraction is append-only
for prior emitted bodies, and all external interface signatures are identical.

The source binding and adaptation --check pass:164 declarations/30files. Every
used span matches the current worktree. The host's unrelated state_only_prefix
loop spelling difference is assessed using the retained predecessor source;
this source reuse is not a new native identity gate. Full per-attempt source
hashes identify the private host tree despite its older revision label.

Continuation Lean launches11524–11550:27 total,23green/4failed; native allocation
51/60, cumulative211/220,9remain. Prior ledgers are unmodified and linked by
hash. Kani44/60 unchanged,16remain. Failed11527 (comparison/abbreviation
elaboration),11530 (dependent status match),11547/11548 (opaque wrapping-add
reduction/tactic failure) remain with exact inputs/logs. Extraction001 failed
before extraction due to PATH; its immutable preflight/time/error logs recover
its receipt (resource peak from ended cgroup unavailable, explicitly recorded).
Corrected extraction002 and expanded003, Aeneas001/002 and read-only hash
inventory have capped receipts. No resource failure or unchanged build retry.

Every Lean attempt kept5G/7G, Rust/translation6G/8G, no swap/Tasks64, populated
reservations below55GiB; after14:00London Lean used the shared global lock.
No full frozen manifest, security-contract change, runtime/performance/ELF
claim, key operation, merge or push. Both deployed targets not yet established.
