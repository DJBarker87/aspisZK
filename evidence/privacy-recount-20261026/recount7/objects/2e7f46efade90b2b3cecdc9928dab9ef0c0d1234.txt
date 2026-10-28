# Frozen outer wrapper extraction status

Charon01 (built MIR) failed before LLBC emission; retained compiler diagnostics.
Charon02 (optimized MIR, exact withdrawal root) emitted error-free LLBC with
opaque ABI types. These opaque records were not accepted as compiler adapters.
Charon03 (optimized MIR, both exact wrapper roots and explicit type includes)
emitted error-free LLBC with both bodies, lane_root, temporary_context and
pair_trace.validate_common. Some newly reached transfer/output types still
need explicit inclusion before any ABI correspondence claim.

Aeneas01 refused Charons03 at its fail-closed preflight:
`ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation`.
The immutable-reference inventory isolates exactly one signature: core slice
Iter::next, id148, opaque, returning Option<&T>. No reference model, source
law, opaque-body success assumption or new T field was introduced. The
backend's check was not bypassed and no backend/launcher was modified.
This is an extraction-route obstruction, not a checked counterexample and
not a stopping reason. Complete an owned/P6 immutable scan association before
claiming source closure for the wrappers. Charon has not proved HonestInput.
