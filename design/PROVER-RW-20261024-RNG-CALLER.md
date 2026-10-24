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
A universal carrier transport remains open.

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

Pending final focused audit and receipt inventory. No full frozen manifest.
