# Native-error callback and cap8 extraction preflight

Branch `codex/cx-prover-rw-20261023`, base `03444c5e5e`. Prototype only;
no shipped source, protocol, wire, feature, security contract, keys, merge,
push or adoption. Target not yet established.

## Established boundary

New `ProverRwRngCaller*` modules contain the concrete emitted callback and
cap8 owner, not a whole-owner equivalence hypothesis. `retry_factor` proves
the actual emitted recursive owner factors through the mechanically checked
`retry_step`. `replay_complete` constructs a finite sequence of those exact
steps for every admitted extraction execution; `replay_sound` executes any
such sequence. `cap8` bounds entered callbacks by eight. `ordered_indices`
proves the sequence of attempt indices is exactly `List.range' initial
trace.length`. The terminal cap guard is included in the trace but excluded
from the callback count. All returned provider, policy, store, body and status
values are retained, including errors. Extraction failure/divergence is not
silently identified with a native error.

`callback_invocation` decomposes every admitted emitted callback into exactly
one actual `FnMut.call_mut` on its incoming policy state, followed by the exact
emitted entropy call on that nonce and provider. The returned policy state is
that invocation's output. No clone/reset, pure input schedule, freshness,
independence, witness-independent retry or source-world equality is assumed.
`native_from` retains the original error value; `callback_step` proves the
actual emitted `map_err` discards either entropy error as `Error::Entropy`.

`zero_reject_fatal` composes three ordered primitive fills of the actual Tape
instance: zero block rejected by entropy, one block accepted by entropy,
body `Rejected`, next policy invocation, next one block accepted, body fatal
`Semantic`. All three buffers are fresh zero64 at the fill call. The conclusion
returns p3/n2/l2/b2, not the states preceding either rejection. The only
premises are two exact policy invocations, admitted nonce scans, three exact
primitive fill replies and two exact body calls. They are local producer
interfaces, not a desired owner equality. Their complete statements and all
hidden structures are printed in the focused audit.

## Native correspondence and retained boundaries

The native Rust prototype uses actual dependency `getrandom::Error` 0.3.4,
original `Os(getrandom::Error)` and source-shaped `From`; all verifier Error
variants are copied for the prover configuration. Source-qualified declarations,
spans, complete signatures, body/signature hashes and every substitution are
in `tools/prover-rw-20261023/rng-caller/source-map.json`. The final LLBC embeds
the exact prototype lib.rs. `step-cut.py` checks the concrete recursion cut
against emitted control; it substitutes only done/cont and return projection.
No cap16 audit/test was repeated.

**Native carrier installation is blocked.** Including Error gives the emitted
definition `getrandom.error.Error := NonZero I32 NonZeroI32Inner`. Including the
core representation fails in Aeneas with unsupported `TPattern` / disjoint
nonzero I32 ranges at core niche_types.rs:20. The failed LLBC, source, command,
exit2 and stack trace are retained. `NativeTypes` provides explicit uninstalled
core type parameters, not axioms or u8 tags. Parametric conversion/control
lemmas do not install those types in the native runtime. The accepted u8
universal cap16 certificate is **not** instantiated at the new carrier. Only
the error-free nonzero scan is reused via checked `scan_same`; new symbolic
constant/error/cap and composed path lemmas check the new emitted definitions.
A universal carrier transport and a general cap8 entropy draw inventory remain
open. The cap8 trace records per-attempt provider states; the three-fill
composition certifies its particular fresh-buffer order.

**Actual body/reservation is a local interface.** Before extraction adaptation,
the native-shaped body cut was
`FnMut(Secrets, &mut L) -> Result<(Vec<u8>, u64), Error>`.
Its emission pattern returns `(result, body, store)` while the pinned standard
FnMut structure only returns `(Output, Self)`. That source/emission is retained;
it was not accepted as a checked theorem. After the explicit substitution it is
`FnMut(Secrets, L) -> (L, Result<(Vec<u8>, u64), Error>)`.
The exact Lean interface is
`FnMut B (StateOnlyAttemptSecrets × L)
  (L × core.result.Result (Vec U8 × U64) Error)`.
There is **no** premise asserting this body equals native execution. The native
producer is `prover::prove_masked_attempt` -> `prove_masked_with_attempt` ->
`StateOnlyAttemptSecrets::reserve_and_build_pool_v1_pair_forest_mask_material_v1`.
The `u64` audit is explicitly a placeholder for MaskedFixtureAudit, with no
association proved. Public/compiled/hash/Variant inputs remain outside this
body cut; the native variant check becomes an explicit `is_s2` input.

The reservation source is pinned in full: layout checks precede durable
reserve; reserve precedes material derivation; pre-reserved acknowledgment is
single use; missing acknowledgment fails; field entropy is explicitly zeroized.
`mask_error` makes only MaskSampleExhausted retryable, with duplicate/reservation
failure fatal. These source facts have not become a concrete extracted Body
instance or a native event/ledger theorem. The duplicate test uses a mock store.
No rollback/refund/key cleanup is introduced or proved.

Native Zeroizing calls remain in the prototype. The existing transparent
value-level new/deref installation and unused ErasureFns remain explicit;
physical drop/zeroization is unproved. The accepted predecessor/prototype
resolves zeroize1.9.1 while native Cargo.lock pins1.8.1: that dependency
association is also open, not a new native identity gate.

E1 remains literally `ProverCommitPublicNonce40.E1`, the conditional successful
64-byte law. Schedule/error history is separate. No probability law was added,
removed or reinterpreted. Native successful bytes/context -> Raw association,
full event/status correspondence and L1/L2 are still open.

## Validation and next producer

The final focused audit J11459 checks proof source revision `f3e9539784`:
exit0, wall2.68s, peak RSS3,846,700KiB, swap0. All27 theorem reports use only
standard axioms (two need none). It prints complete theorem statements,
carrier/erasure/FnMut/Body/Replay structures and concrete emitted owner bodies.
Receipts retain exact commands, source/dependency hashes, full diagnostics,
axioms, resource limits and time. No full frozen manifest.

Continuation J11440–11459 used all20 actual Lean launches:10 green,10 failed.
Owner allocation is60/60, stage3 remains100/100, cumulative160/160. Kani stays
44/60, all16 unused runs retained. Failures11441/42 (tuple normalization and
Result-typed addition),11444 (generated discriminant global-name collision),
11447/49 (extra carrier parameter and unused predecessor erasure parameter),
11448/50 (qualified Error and opaque cap),11453 (tuple continuation),11456/57
(dependent case rewrite) are retained verbatim. No failed result is accepted.
The new annotations remove only discriminant attributes that generated global
names colliding with cap16; emitted types/control are retained. The original
40-attempt owner ledger and exhausted stage3 ledger are unchanged.

New Rust validation: four optimized Charon attempts, four capped Aeneas
attempts (the third failed on the native niche pattern), and two optimized
runs of four finite stateful tests after moving the fixture from embedded to
separate test target. Both runs pass. Tests cover changing zero/one/two replies,
mutable nonce state, native custom error conversion/mapping, duplicate fatal
exit retaining provider/store state, eight-rejection exhaustion and variant
no-callback guard. They do not prove native durable-store semantics. The raw
borrowed-body emission exposes the FnMut return mismatch; that item was stopped
without treating its output as a checked native refinement.

Every launch preserves Lean5G/7G or Rust6G/8G, no swap and TasksMax64; populated
reservations are checked below55GiB. No resource failure, cap increase,
heartbeat/recursion override or unchanged heavy rerun. The raw Aeneas templates
retain original generated settings and axiom placeholders as evidence only;
the imported adaptation removes those settings and supplies no axiom.
The `step-cut.py` and `bind.py --check` pass; generator/adaptation reproduce the
same checked source hashes without replay. Each derived JSON is below5MB.
`summary.json`, all raw receipts and `artifact-hashes.json` are in
`docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-caller/`.

Next concrete deliverable: support/check the core nonzero-I32 validity type in
the pinned extraction chain (or a separately justified source representation
map), then prove native-error cap16 transport rather than substituting types.
Next body producer is the actual reservation/build path identified above,
including layout, durable failure/duplicate, single-use acknowledgment and
native audit/status effects. An owned-store interface does not discharge it.
Further Lean work needs a new allocation; this ledger must not reset.

Native integration remains a later authorized change: provider leaf and selected
caller ownership, exact error/proof/audit/ledger/event relation, physical cleanup,
then separate successful bytes/context-to-Raw association with literal E1.
Proof impact: these are reusable local predecessors only. Runtime, artifact
and performance impact: none established for native source in this stage.
No ELF or timing gate ran. Later adoption still requires all3 current default
f8c0/devnet63ad/Pool121f identities, complete event/status equivalence,
H5 interleaved slowdown≤10%, quiet-host<15s. Final host activity was rechecked;
the old z3PID2095724 is absent, but this is not a quiet-host timing claim.

The installed core rust-src matches emitted map_err line962 and the core
NonZero/niche declarations; hashes and complete relevant snippets are retained
in `core-source-assessment.json`. The transparent map_err installation follows
its two source match branches. This source assessment does not install native
layout or physical destruction semantics. Raw inputs/time/logs stay immutable;
enriched receipts add effective Lean command/path and full revision resolution.
Attempts11440–11458 label their parent revision plus immutable work-in-progress
source snapshots;11459 checks the exact committed proof source.
