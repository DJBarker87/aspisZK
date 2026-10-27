# Six-input deployment inventory

Evidence only; no adoption. **Target not yet established.**
`IDb_Components` supplies two complete effective source dictionaries.
`IDb_Deployed.deployedConfigurationFull` names the four unresolved inputs:
`adapter currentBase stageBase reserved`, plus the inherited error value
`indexError : CoreError` and allocation `reservation : NP6_StdModel.Reservation`.
“Full” describes the field inventory, not a parameter-free runtime certificate.

## Per-input decision and provenance

| IDa input | Defining component, actual installer and extraction/source provenance | IDb disposition | D188 coverage |
|---|---|---|---|
| adapter | `AdapterRw.Ops` in `docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:19`; Aeneas function model for `aspis_r1_cost_probe_program`, owned `r1_pool_adapter` stage1/stage2 source. `Rc5_Install.seed` calls `CPP_Install.configuration` (op35 clone VALUE, op36 `Hist_Authority.keyEq`). `DrvC_Installation.sdk` → `DrvI_Installation.sdk` → `Tx2I_Install.install` and `ClaimsUnrolledSdk.sdkOps` installs TX2/TX1 callers. | **Retained named adapter.** No seed-free complete SDK dictionary in that chain. `IDb_Deployed.digest_residual` checks effective op43 is still adapter.op43. Selecting hashv separately does not define op43; the actual extraction.digestSource law still binds them. | Retained D188 stage1/stage2/digestSource trust on the SAME selected dictionary, no new body association. No complete release-instance certificate supplied. |
| currentBase | `AspisR1CurrentCaller.Ops` is the emitted external-operation dictionary of the current-caller kit. Retained generated source: `docs/research/100bit-spend-path-20261013/evidence/s4-candidate-prepare-s1-parent-v1-20261022/source-pins/AspisR1CurrentCaller-Funs.lean`; the namespace/type owner is imported through the coherent SInt2 objects. `Uni_Install.current` composes `Tx1Q_Execution.base`, `Op4P_Install`, `Op5T_Concrete.current`, `Op3I_Install`; `RowShape_InstalledSlots.verifierOps` then installs NativeBuffers, values, round children and Claims. | **Retained named currentBase.** These are dictionary updates requiring a seed, not a complete constructor. `current_field` checks the Configuration input is preserved. The installed current dictionary may overwrite some/all relevant callbacks in a particular execution; no full seed-independence/closed original-carrier construction is supplied here. | Cohort association is qualified by D188-P2: retired PublicPreparation/ExtractedTx1Model interfaces. No claim of release extraction coverage for the complete currentBase. |
| stageBase | `VTop_Stages.Ops` in `docs/research/100bit-spend-path-20261013/lean/VTop_Model.lean:19`, emission adapter over retained `evidence/verifier-top-20261023/generated-complete/VTop_Stages/Funs.lean.txt`. Header identifies candidate.tx1, `crates/aspis-r1-cost-probe/src/candidate.rs:270–291`. `DrvC_Implementation.release` fixes `Port1_Library.install (Port1_Library.std stageBase)`; `AuS1_Install.base` offsets/unwrap; `DrvI_Installation.stage` → Tx2N/Op5T/Tx2I fixes reader/query/flush/powers/geometry/shape/finish. | **Retained named stageBase.** `stage_field` checks the raw release update; `stage_scan_residual` checks effective op4 still equals stageBase.op4. The adopted installer does not select this scan callback. A separately named scan body is not automatically a typed, installed whole dictionary. | Partial emitted source body, not a complete release dictionary. D188/P6/P7 and SAME-source association remain. |
| reserved | `Bool` consumed by `Port3_Initial.constructor`, `CheckpointBytes3Allocation.filled`, `Port3_NativePendingInstall.source`, and `Port4A_ReaderInstall.reader`; `Tx1Q_PrefixInstall.install`/`Tx2N_Execution.control` pass it through. | **Retained named reserved.** An allocation outcome, not a source constant. Native acceptance can imply success at reached allocations but does not define a universal runtime allocator; fixing true here would preselect allocation behaviour. Distinct from the richer `reservation` Result used by Claims/Pair. | Runtime/environment value; neither extracted code nor a D188 release constant. No new allocator trust introduced. |
| query | `Port3_NativeQueryBody.Ops` in the historical docs lean tree. Header identifies verifier.rs query/accumulation bodies. `Rc5` → `SAQ_Decoder.install` → LineQuery/QuerySource/Arithmetic/Query sets arithmetic, line, decoder; `FIp_Install.select` fixes circle/dots/equality. Actual consumers apply `Port4C_RowStd`, `Port5Q1_QueryPorts`, `Port3_QueryStage.release`. | **Resolved to IDb_Components.query.** Complete 23-field record. `query_consumer` proves every such selected seed gives this same TX1 leaf dictionary. `query_release` checks the TX2 consumer order gives the same record. `query_fixed` proves Rc5/FIp selection preserves the supplied record. | **Cohort/composed source-model coverage only, not a new D188 release-extraction certificate.** Includes extracted arithmetic/decode/dots fragments and reference std/ABI/control interpretations. SAME query powers/openings/carrier and D188-P2 release association remain deployment gates. |
| geometry | `Port3_NativeGeometryBody.Ops CoreError`, docs lean tree, retained source headers `verifier.QueryGeometry.for_range`, verifier.rs:148–177, plus emitted loops. `Rc5` → `SAQ_Constructor.install` → GeometrySource/Geometry fixes index/arithmetic/inverse/point/line. `Port5Q1_GeometryTerminal.install` fills std, native prefix, collector. | **Resolved to IDb_Components.geometry indexError.** Complete 17-field record including mapIterator. `geometry_consumer` proves the entire effective dictionary independent of seed, including prefixCall's closure over already-selected op9/op7. `geometry_selected`/`geometry_fixed` check both installation stages. | **Cohort/composed source-model coverage only.** Native prefix and extracted scalar/domain bodies reused, but cache/interface association (`line_z`) across the release preparation/query boundary remains D188-P2. No whole-release translation or ELF claim. |

## Complete resolved field selections

`IDb_Components.query` spells out every field, with no failure defaults or
fixture callbacks: op0 ordered `OraclePortStdBuilder.fromFn`; op1/op10 RowStd
embeddings; op2/op9 SAQ arithmetic; op3 mixed native multiply; op4/op5 zero/one;
op6/op7 current M31 sub/mul; op8 S7 double; op11 opening slice; op12/op13 actual
slice/array reads; op14 native row push; op15 release trace; op16 SAQ line;
op17 FIp circle; op18 geometry accessor; op19 release mark; op20 FIp dots;
op21 SAQ decode; widePartialEq FIp equality. These are exactly the existing
installer choices, not a new mathematical evaluator.

Geometry similarly spells out ordered fromFn/iterMap/mapIterator; Result mapError;
short-circuit any; Vec empty and raw equality; M31 zero/one/sub/mul/double;
SAQ inverse/fibre/line/point; and native prefix products with the SAME selected
mul/one. It does not assume nonzero inputs or successful inverse/allocation.

The remaining Configuration fields are exactly IDa's finish, boundaries and
std (see IDa_DEPLOYED-CONFIG.md for all 12+8+2 leaves). Terminal remains
`FIq_Terminal.terminal`; finish is the FIo/FIn source/value interpretation;
std is the Rc2 `NP6_StdModel.calls reservation`. Every one of the nine fields
has a named projection theorem; `top_fields` checks the top's further FIp
installation preserves each. No whole-record normalization is required.

## What resolving means

Two implementation-data inputs are removed from this family, **zero counted
security premises**. The top's Configuration is specialized; arbitrary native
functions still require the original D188 association. A source header is
provenance, not proof that today's frozen ELF executes this entire composed
dictionary. Four unresolved inputs are explicitly quantified, not hidden in a
record or chosen with Classical.choice. The task's parameter-free alternative
is therefore not established. No ELF rebuild trigger: no shipped file changed.
