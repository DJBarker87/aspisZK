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

## Exact operational call chain

`tools/r1-cost-probe/src/bin/devnet_spend/plan.rs:105` selects the transfer or
withdrawal forest compiler, propagates its error, and only then invokes
`RealR1_client::prove_for_proof_accounts` at line 116. The adapter itself
accepts compiled data. The source domain condition is established by those
entry checks, rather than by the adapter name or a raw-mapper postcondition.
The predecessor mathematical fixture constants and the live planner's
account-derived witness are distinct carriers; native association remains
explicit, and a mathematical fixture theorem is not a byte/installation claim.

## Draft obligations prepared during the hold

Thirty new module drafts are dependency-ordered in `draft-order.json`. They
cover successful common-validation inversion, canonical request amount,
forward fixture pair/common validation, scalar reduction, pure callback
totality, successful snapshot preservation, public projection subfields,
primitive-stage fixture non-vacuity and the unchanged four-field consumer.
Only CheckedEncoding has compiled at this point (receipt 25301); every other
draft remains unverified. The process exception is recorded in QUIET-WINDOW.md.

The proposed four-field remainder is parameterized by a selected family
`I → CheckedCanonical.Data`, not by every arbitrary supplied compilation.
This matters: requiring all possible supplied compiled payloads to succeed
would make the remainder inconsistent. It retains the original four field
statements, omits only words, and obtains words from the proved canonical
encoding under the dynamic reference dictionary. No RspendPlus, trace
equality or successful compiler call is smuggled into a data definition.
Actual mapper P6 and installed input association remain separate obligations.
