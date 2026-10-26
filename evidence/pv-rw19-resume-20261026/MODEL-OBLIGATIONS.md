# Exact residuals while gated

All thirteen rw19 modules are drafts, including the nine inherited modules.

V164 before: `ProverRw18ContextJoin.callback` takes
`source_law : ops.op223 = extracted` and
`context_identity : extracted = @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)`.
Checked after: unchanged. The P6 draft proves context identity for the concrete
retained extraction; its consumer keeps exactly
`P_source_p6 : ops.op223 = @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)`.
Neither an unconstrained dictionary nor a bounded native test supplies this
universal function equality. No original-helper extraction is asserted.

V163 before: `ProverRw18ContextDataIff.criterion` requires the independent
whole-model result and both observation equalities. Checked after: unchanged.
For a canonical audit the audit equation follows from the byte equation,
including rejection, failure and divergence; it is not separately assumed.
The original-caller criterion leaves the following exact right-hand side:

```lean
PV_RW_DataProduct.observe PV_RW_DataProduct.first
  (ProverRwBodyDataCriterion.data
    (ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s)) = modelBytes
```

This is `P_proof_bytes`, still OPEN, with precisely the theorem's input
quantifiers and `reservation` equation; it is not hidden in a structure.
`modelBytes` must come from the mathematical deployed-caller model. No choice
of source output as that function is permitted.

The independent mathematical assembly adapter uses
`ProverCommitFront46.referenceProof fields queries slots`, preserving its
errors and both length guards. Its inputs still require construction from the
mathematical protocol for the deployed caller; it is a serialization model,
not the complete mathematical instance. In particular it supplies neither
release fixture's whole-model equation, nor the general byte equation.

Next focused validation order: P6ContextIdentity, P6Join, P6Caller;
AuditValue, AuditSource, AuditData, AuditCaller; CanonicalAuditRefinement,
P6DataIff; CanonicalAuditCriterion, OriginalAuditCriterion; AssemblyLength,
MathematicalAssembly. Audit and manifest only after these targets are green.
No frozen manifest changes while these sources remain unchecked.
