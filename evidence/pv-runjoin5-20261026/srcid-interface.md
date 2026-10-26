# Exact srcid interface (in progress)

Checked export: `R1Z.PV_RunJoin_InstalledTransport.endpoint_row_call` in
`PV_RunJoin_InstalledTransport.lean`. Import `R1Z.PV_RunJoin_InstalledTransport`.
Exact statement:

```
∀ j : Fin 1024,
 (PhaseWireLog2Bin.honest PV_RunJoin_SourceEndpoint.input).transport j =
 PV_Src_Transport.row j
```

`endpoint_transport` gives equality with `PV_Src_Transport.transport` as an
Equiv. Standard axioms only (25638). This specializes the row_call premise at
THE fixed endpoint honest caller. It does not assert an equality for arbitrary
free transport data, and does not discharge native bitwise op255 association.
Read-only sibling source and revision pin: srcid-transport-read-pin.json.

Selected input DATA interface `PV_RunJoin_SelectedInputs` is drafted and next
for focused checking. It takes an ACTUAL PV_Src_NativeInput.Input selected
record, reads that record's compiled field and publicInput through explicit
nominal extraction projections, and uses one common hash/dictionary. Actual
nominal source identities and the installed selected-record RspendPlus premise
remain to prove; no arbitrary record is called an installed native record.
