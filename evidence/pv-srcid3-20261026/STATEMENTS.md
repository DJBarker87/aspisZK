# Selected-input range discharge

Target not yet established. This continuation supersedes the predecessor's
stop rationale: the raw mapper diagnostic is not a counterexample to V152–V154.

The exact condition excluding `merged[10][1010] = 2^30` is
`PV_Src_RecordReference.Checked.values.2.1`:
`(PV_Src_NativeInput.outputValue i.request).val < 2^30`.
`WitnessOk.values.2.1` requires that same strict bound on the returned output
word. The raw mapper copies that value without reducing it.

The selected client `RealR1_client::prove_for_proof_accounts` accepts a compiled
object; it does not itself validate witness values. The operational caller
constructs this object with the forest entry wrappers. Transfer checks recipient
and change values against `VALUE_LIMIT = 1 << 30` at
`crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:416–424`.
Withdrawal validates the temporary withdrawal public, which includes the amount
bound, then checks the change bound/conservation at lines 453–472. Both invoke
`validate_common` for the input value, pair commitments and membership siblings;
the full compiler rejects noncanonical super-root siblings at lines 319–326.
The route is documented in `design/PV-CLIENT-ROUTE-20261026.md`, under D162.
These are source locations, not yet a universal formal caller association.

Canonical mathematical admission is `BuilderCanonical.Instance`: its Wspend
values are `Fin (2^30)`, and field digests encode as canonical M31 words.
`RspendPlus` retains all original spend/append/sentinel conditions. We will
prove primitive `Checked` for its native encoding rather than infer it from
an unconditional raw-callee law. Full installed input/transport selection
remains the explicitly named pv-runjoin5 interface.

Budget: 96 new Lean attempts (4 predecessor attempts retained), 12 Kani runs.
Env-J 25300–25599. Quiet hold: 2026-10-26 17:45–18:15 UTC; no capped launch
during the hold. No frozen source modifications are authorized.
