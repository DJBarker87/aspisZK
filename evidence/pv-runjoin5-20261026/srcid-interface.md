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

## Checked concrete record projection

Import `R1Z.PV_RunJoin_NativeSelectedInputs` (25649). This replaces the earlier
generic draft interface. Use `inputs base ops hash i` for the source-header
body or `ledgerInputs base ops hash i` for the ledger-world body, with THE
actual `i : PV_Src_NativeInput.Input` selected by the caller. For a family,
use `fun h x w => inputs base ops hash (selected h x w)` (or ledgerInputs).
The compiled field is fixed to `NominalCompiledData.compiled base i.compiled`;
the public field is fixed to `NominalPublicData.fromInput base i`; the hash
and state-dependent primitive dictionary are common explicit inputs. The
dictionary is exactly `PDict_CodecDictionary.selected base (ops state)`.
There is no free compiled-value projection or nominal adapter hypothesis.

Checked exports:
- NativeSelectedInputs.same_selected_compilation (25649), exact selected
  record compilation read.
- NativeSelectedInputs.full_ledger_source (25649), full emitted body source
  law, with map_err discharged by dict10's actual selector (25648).
- NominalCompiledData.compiled_roundtrip (25646), every compilation field
  preserved, including trace metadata, semantic columns and public statement.
- NominalPublicData.selected_public (25647), public value equals translation
  of publicInput of that SAME record.
- InstalledTransport.endpoint_row_call (25638), fixed endpoint transport.

Still required: the actual selected family, compiler success on those inputs,
selected-record RspendPlus, and source/public association. No arbitrary
PV_Src_NativeInput.Input is declared admitted or successfully compiled.
No complete native Runtime/Boundary or observer decoder is installed by these
constructors; original native endpoint counts remain2→2 and8→8, residual6→6.
