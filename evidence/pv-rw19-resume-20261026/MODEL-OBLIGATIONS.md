# Checked residual obligations after the resume

V164 before (`ProverRw18ContextJoin.callback`):

```lean
source_law : ops.op223 = extracted
context_identity : extracted =
  @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
```

V164 after, for the concrete retained owned P6 extraction, in the checked
`ProverRw19P6Join.callback` and `.dictionaries`:

```lean
P_source_p6 : ops.op223 =
  @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)
```

`ProverRw19P6ContextIdentity.identity` supplies the second equation; it is no
longer assumed in this consumer. The formerly arbitrary `extracted` argument is
specialized to the concrete P6 reference. No original whole-helper extraction
or shipped-to-P6 function law is asserted. Published rw18 statements remain stable.
The latest read-only cb3 search at `80ef4e8e3daa17e1966559bd69fb946eb5eeaf07`
found no op223 theorem. V164 remains REDUCED, not closed.

V163 remains OPEN. Before, `ProverRw18ContextDataIff.criterion` required the
concrete whole-model instance and both observation equations. After, the
checked `ProverRw19AssemblyCallerIff.criterion` supplies the exact conditional
criterion for an independently assembled mathematical output, with no audit
observation premise. Its single residual byte equation is:

```lean
P_proof_bytes :
  PV_RW_DataProduct.observe PV_RW_DataProduct.first
    (ProverRwBodyDataCriterion.data
      (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
        store pub compiled v hash binding digest attempt s)) =
    ProverRw19MathematicalAssembly.proofBytes fields queries slots
```

The full theorem retains `P_source_p6` above and the unchanged state equation:

```lean
reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after)
```

The arbitrary input quantifiers and both Result layers are preserved. Error,
failure and divergence are included. The independent preparation wrapper also
preserves all verifier errors, failure and divergence, but its mathematical
preparation function for the deployed caller is **not constructed**. Fields,
query parts and node slots are data, not structures containing assumed laws.
No model is defined by projecting the actual source result.

Neither full release fixture's byte equation nor the general byte equation is
proved. Thus this model-family specialization is not closure of the original
whole-model criterion. No privacy headline premise has been removed or weakened.

The auxiliary `P_proof_size : compact.PROOF_BYTES = ok size` is retained in
generic publication/body length theorems, then discharged for the installed
original and closed dictionaries. `ProverRw19SelectedBodyLength.original`
proves successful original-caller proofs have 57,607 bytes without that premise.
A length invariant is not proof-byte correspondence.
