# Native boundary and non-vacuity

V404 and V405 remain OPEN. No new fixture-admission premise is introduced by
any prefix certificate. Prefix certificates quantify over the extracted
public/compiled carriers; they do not select or admit a native fixture.
Their first-bind equalities alone are not complete execution trace theorems.

The missing native compiler-success hypothesis has exactly this type, with
`external : BuilderForestAdmissionPort.ExternalLinear`,
`records : BuilderForestAdmissionPort.Records`, and
`inputs : Bool → R1Z.PV_Src_NativeInput.Input`:

```lean
compile_call : ∀ withdrawal,
  @R1Z.PV_Src_NativeInput.run external records (inputs withdrawal) =
    Aeneas.Std.Result.ok (.Ok (inputs withdrawal).compiled)
```

The returned payload/public association is the existing, unmodified type:

```lean
association :
  R1Z.PV_Src_PublicDeploymentAssociation.Association records inputs
```

Its fields are `snapshot`, `frontier`, and `returned_public`; their exact
definition is in `PV_Src_PublicDeploymentAssociation.lean`. These are P
obligations, not T fields. The actual records dictionary is not instantiated
here. In particular, an arbitrary `inputs` function or successful abstract
compiler result is not a native fixture witness.

The complete primitive/admission boundary remains the existing
`@R1Z.PV_Src_NativeIdentification.PV_Src_Premises K _ _ external records
Bool inputs transport`, including `compile_call`, `words`, `publicCorr`,
`admission`, and `row_call`. No field is discharged by this job.

Non-vacuity on `inputs false` (transfer) and `inputs true` (withdrawal) is
**not established** for either compiler success or the native association.
The existing mathematical fixture fibres do not establish these native
hypotheses. There is consequently no conditional fixture closure or row
removal claim in this job. V163/V167 are retained unchanged.

The only explicit Prop hypothesis added to the initial source helper is
`ops.op226 pub = .fail e` in `PV_RE_AttemptEntry.failure`. It is a generic
failure guard, not a fixture premise. It has not been instantiated on the
selected native transfer/withdrawal dictionaries and earns no fixture
exclusion credit. The remaining generated prefix/guard equations add no
Prop hypotheses. Typeclass carriers remain abstract, not deployed instances.
