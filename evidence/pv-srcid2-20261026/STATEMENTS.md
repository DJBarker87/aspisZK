# Native premise-family audit

Base: d385c8908f, branch codex/pv-srcid2-20261026. Target not yet established.
The exact five fields, in requested order (unchanged):

```lean
  compile_call : ∀ i, run (inputs i) = ok (.Ok (inputs i).compiled)
  words : ∀ i records, newRecords (inputs i) = ok records →
    WitnessOk (wordWitness records.w)
  publicCorr : ∀ i records, newRecords (inputs i) = ok records →
    PubCorr (wordPublic records.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
  admission : ∀ i records, newRecords (inputs i) = ok records →
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

```

## compile_call

Before = after: the field above, including both Result layers.
Classification: OPEN pure callee-success obligation, plus selection of valid
inputs and the actual returned payload at the caller boundary. D188 applies to
the extracted compiler; it does not supply implementations of Records.call
and ExternalLinear.call. These are explicit uninterpreted dictionary fields
in BuilderForestAdmissionPort (lines 4362 and 1865). They are not effects.
No reduction or premise discharge is claimed at this stage.

The canonical stage certificate uses encoded records directly. It does not
construct a successful native compiler execution for either release fixture.
Reusing that certificate as compile_call would change the statement.

| Family | Before fields | After fields | Status |
|---|---:|---:|---|
| compile_call | 5 | 5 | OPEN: actual callee/reference implementations and valid-input run proof |

No new Lean theorem is asserted in this commit; no compile receipt is claimed.
