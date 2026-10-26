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

## Compiled reference-side results (18:21 UTC checkpoint)

CheckedEncoding, CheckedValidation, CheckedVariants, CheckedFixtures,
CanonicalRequest, RecordDynamic, CheckedCanonical, SelectedFour and
SelectedConsumer are green. The four-field remainder genuinely omits words
and the unchanged BuilderPremises consumer accepts it, but its dictionary
is the explicit dynamic owned reference and selected inputs are canonical
encodings. This is **5 → 4 for that reference-side selected family**, not a
claim that the deployed native endpoint's five fields have become four.
Unstubbed P6 and installed selection still require their evidence.

ReturnedSnapshot, RecordDynamicResult, PublicHeader and PublicParts are green.
On successful compilation the constructor/returned-public association supplies
variant, asset, next and frontier. Remaining pure publicCorr inputs are exactly:

```
∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!
∀ roots, pair_empty_roots = ok roots → ∀ l : Fin 20,
  DigestLift roots.val[l.val]! (emptyRootK l)
∀ roots, pair_empty_roots = ok roots → ∀ l : Fin 20,
  Canon8 roots.val[l.val]!
```

These are pure source obligations, not effects. BanksTotal/CheckedPipeline
prove successful record construction, WitnessOk and successful optional bank
return for both canonical fixture carriers, for every supplied root table.
They do not yet prove a successful dynamic root call or full forest compiler.

25326 was refused by aggregate reservation at 18:21:00 UTC, charged zero.
Earliest retry is 18:24:00 UTC with the next unused ID, 25327.

## Frozen-reference next statement (draft)

The retained root certificates cover all 21 fixed source calls and their exact
21-call composition (P6 Kani/CBMC soundness). The five relevant source files
are byte-identical to the accepted historical revision; the only current
root-harness overlay is a new cfg(kani)-only accessor, whose unchanged prefix
is recorded in root-certificate-inventory.json.

The new full-mapper harness compares the actual unstubbed mapper (including
its root helper) to the extracted owned reference on that fixed frozen table.
It does not stub roots or raw words. This strengthens the pending check so
that a successful P6 result can feed both words and the public root fields.

A further draft selects the canonical snapshot encoding as data, rather than
assuming its canonicality in publicCorr. Given the original compile_call,
ReturnedSnapshot identifies its snapshot with the returned compilation, and
PublicParts plus the frozen root table then proves the entire seven-field
publicCorr. The proposed three-field remainder retains compile_call, exact
selected-record RspendPlus and exact installed transport equality. This is a
proposed reference-side 5→3 reduction until those new modules compile and the
unstubbed P6/installed-caller joins have their evidence. No endpoint row is
credited here on the basis of a draft or historical root evidence alone.
