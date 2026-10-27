# Field stub and emitted-value pairings

Stage 1 and subsequent value ports: compiled L001, L003–L007, L010–L012, L017. L002 stopped at the inherited cache's missing PAln_RowBounds; full closure inventoried once, then the lead-designated coherent RPv/RPu/RPt/RPz replay cohort reused. No theorem statement was weakened. All successful axiom audits contain only propext/Classical.choice/Quot.sound, or none.

Every replacement returns `kani::any()` constrained with `kani::assume` to the natural coordinate specification. Every input-domain test is an **assertion**, so a caller cannot acquire canonicality by assumption inside a stub. Stub sources are scratch-only in LPh_field_stubs.patch. No multiplication equivalence is attempted in Kani.

| Rust replacement | Emitted operation / named Lean value theorem | Domain |
|---|---|---|
| field::LPh_stubs::m31 | FIo_Native field.M31.mul; LPh.Native.m31_value (L003) | all inputs U32 for theorem; stub checks both <P |
| field::LPh_stubs::cm31 | FIo_Native field.CM31.mul; LPh.Native.cm_mul_expanded (L010) | each of four input words <P |
| field::LPh_stubs::qm31 | FIo_Native field.QM31.mul; LPh.Native.qm_mul_expanded (L007) | all eight input words <P |
| field::LPh_stubs::scalar | FIo_Native field.QM31.mul_m31; LPh.Native.qm_scalar_value (L003) | theorem all U32; stub checks four words and scalar <P |
| field::LPh_stubs::by_r | FIo_Native field.mul_by_r; LPh.Native.by_r_expanded (L011) | both words <P; helper private, callers stub the enclosing public op or use an in-core harness |
| field::LPh_stubs::wide | FIo_Native field.wide_exact.WideExact.mul; LPh.Native.wide_mul_expanded (L012) | every coordinate of both inputs <P; public WideExact constructors enforce this |

P=2147483647. L007/L010/L011/L012 close the explicit expansion stage: each native emitted operation returns ok with the exact natural modular coordinate expressions used by the Rust replacement, plus canonical outputs. The projection-only intermediates (L005) are strengthened through the unchanged probe word/exact lemmas and existing native linear-operation bridges. The CM31/QM31/Wide replacements have no remaining value-theorem gap. No translated-field stub caller is credited here: the ten-leaf consumer domains and SAME carriers remain separate obligations. The actual Dot consumer uses the additional raw stub below.

L001 separately transports the existing probe Nat word formulas to the SemanticCall extraction: m31_mul_value, cm31_mul_value, qm31_mul_value, mul_by_r_value. Those carriers are not silently identified with FIo_Native. Failed L008/L009 diagnostics are superseded by L010 and are not imported.

## Dot raw boundary

Dot::push calls Q::raw, not the field operations above. The checked theorem AspisR1.FJf_RawReference.source gives the actual FIo_Native Q.raw successful result, in four explicit word expressions. A raw replacement must be paired with that theorem on exactly the same packed operands; field multiplication stubs alone do not replace this obligation. Native/model packed-array association remains distinct from the value theorem.

| Additional replacement | Paired theorem | Domain and consumer result |
|---|---|---|
| canonical::LPh_dot::raw_stub (including its ghost output observation) | AspisR1.LPh.Raw.value, L006; inherited FJf_RawReference.source | packed eight U32; stub asserts each <P, established by each caller's checked Q constructor. K004–K007 PASS conditional four coordinate updates. SAME packed-array/source-model carrier installation remains OPEN. |

## Shared raw Nat port and import obstruction

L017 `AspisR1.LPh.Raw.raw_nat` proves that the emitted native raw result has exactly `LPh.RawSpec.rawNat`'s four Nat words, including every wrap and partial fold. L058 `AspisR1.LPh.Model.raw_words` proves that the old XRk model has exactly that same specification on the same eight packed U32 words. These are separately checked ports, not a jointly imported theorem. L056's attempted composition is blocked at import by the pre-existing generated global instance collision: `XRk_Types` already contains `instDiscriminantErrorIsize` from `AspisR1FinishRelationCurrent.Types`. Failed source and exact error are retained. No existing generated module or other worker's candidates were modified to mask it. Joint context/carrier installation is OPEN.
