# Native witness boundary review

V163,V167,V404,V405 remain OPEN. The new original-client prefixes end at context/tag/encode/second hash and, conditionally, the reserve-and-material call. They prove no native compiler success, native proof byte/audit equation, or ordered-effect law.

The exact inherited boundaries are retained, with no replacement by T:

```lean
compile_call : ∀ withdrawal,
  @R1Z.PV_Src_NativeInput.run external records (inputs withdrawal) =
    Aeneas.Std.Result.ok (.Ok (inputs withdrawal).compiled)
association : R1Z.PV_Src_PublicDeploymentAssociation.Association records inputs
external_law : R1Z.PV_Src_ExternalAssociation.Associated external
records_law : R1Z.PV_Src_RecordAssociation.Associated external records
```

The complete NativeIdentification.PV_Src_Premises still includes words, publicCorr, admission and row_call. Its compile_call is a native P obligation. Actual records and inputs false/true have not been instantiated with these laws. No existential package of these assumptions is presented as their non-vacuity witness.

Source inspection: PV_Src_FrozenFixtures.both_primitive and both_inhabited leave compiled, anchor and pool/domain/destination as parameters. PV_Src_CheckedFixtures.both_inhabited proves the Checked stage only. PV_Src_Fixtures.fixture_run uses the smaller ForestTrace run. Their own comments correctly distinguish these stages from successful full native compiler/caller execution. These results do not instantiate compile_call or the installed associations above. PV_Join_FixtureInputs.same_record nominally preserves the supplied compiler record; its comments also retain native compiler success separately. No duplicate native fixture-success credit is taken.

No conditional whole-client native success witness or proof of the native hypotheses' non-vacuity has been completed. The new success_distinguishes theorems explicitly assume a successful extracted client result, in addition to the listed source-prefix equations. Their statements must not be described as fixtures succeeding.

The D188 fidelity suspension/restoration rules remain intact: these are equations over the pinned emission. No new Rust/emission source law or iterator-write fidelity claim is made; the inherited fidelity frontier and V167 ordered effects/failure/divergence obligations remain.
