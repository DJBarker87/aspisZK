# Exact retained boundaries and comparison

`PV_RE_InstalledOp84B9.installed_noCatch` has the same binders and conclusion
as the failed original InstalledOp84 candidate. It quantifies over base,
ops at CandidateDictionary.native base, tag and values. It proves that a
failed or divergent pending hash is forwarded by the installed op84. There
is no success, fixture admission, complete invocation trace or excluded-entry
conclusion. The manifest checks the statement text is identical.

`PV_RE_ReserveGuards9.client_to_store` fixes the dictionary to
`ProverRwOuterMapErr.selected ops`, rather than arbitrary ExternalFuns. The
source installation discharges five old prefix hypotheses: variant equality,
map_err success, context construction, tag and encoding. The nonce and two
fingerprint checks are discharged by OuterGuardBridge.checked. The conclusion
factors the actual proof-account client at the actual durable-store reserve
call, with the entire suffix retained.

Its four prefix equations remain `entropy_prefix`, `serialization`,
`first_hash` and `second_hash`; their exact types are printed in audit A.
They have not been instantiated jointly on either native fixture. This is a
source-selected conditional transport theorem, not an unconditional fixture
witness or a premise removal from the deployed endpoint. The theorem does
not assume a successful whole client.

The native P boundaries remain exactly:

```lean
compile_call : ∀ withdrawal,
  @R1Z.PV_Src_NativeInput.run external records (inputs withdrawal) =
    Aeneas.Std.Result.ok (.Ok (inputs withdrawal).compiled)
association : R1Z.PV_Src_PublicDeploymentAssociation.Association records inputs
external_law : R1Z.PV_Src_ExternalAssociation.Associated external
records_law : R1Z.PV_Src_RecordAssociation.Associated external records
```

The full NativeIdentification.PV_Src_Premises additionally retains words,
publicCorr, admission and row_call. No P field is folded into T. The native
record association, ordered effects, failure/divergence and whole proof/audit
data equations remain V163/V167 obligations. No native differential or D188
fidelity credit is added by these emission-level proofs.

The inherited FrozenFixtures theorems concern the smaller reference records.
Their compiled, anchor, pool/domain/destination parameters are visible in the
reserved statement audit. They are not native compiler or whole-client
success witnesses. Their false/true carrier facts are not promoted to the
required native non-vacuity.

For both V404 and V405, complete admitted-input reached sets and minimality
remain unproved; no actual universal callback exclusion is added. U255
source support and Result replacement invariance remain distinct from
execution/invocation evidence. No endpoint statement, deployment condition,
simulator, observer or trust field changes.
