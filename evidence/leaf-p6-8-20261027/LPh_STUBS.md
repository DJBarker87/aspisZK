# Field stub and emitted-value pairings

Stage 1: compiled L001, L003–L005. L002 stopped at the inherited cache's missing PAln_RowBounds; full closure inventoried once, then the lead-designated coherent RPv/RPu/RPt/RPz replay cohort reused. No theorem statement was weakened. All successful axiom audits contain only propext/Classical.choice/Quot.sound, or none.

Every replacement returns `kani::any()` constrained with `kani::assume` to the natural coordinate specification. Every input-domain test is an **assertion**, so a caller cannot acquire canonicality by assumption inside a stub. Stub sources are scratch-only in LPh_field_stubs.patch. No multiplication equivalence is attempted in Kani.

| Rust replacement | Emitted operation / named Lean value theorem | Domain |
|---|---|---|
| field::LPh_stubs::m31 | FIo_Native field.M31.mul; LPh.Native.m31_value (L003) | all inputs U32 for theorem; stub checks both <P |
| field::LPh_stubs::cm31 | FIo_Native field.CM31.mul; LPh.Native.cm_mul_words (L005) | each of four input words <P |
| field::LPh_stubs::qm31 | FIo_Native field.QM31.mul; LPh.Native.qm_mul_words (L005) | all eight input words <P |
| field::LPh_stubs::scalar | FIo_Native field.QM31.mul_m31; LPh.Native.qm_scalar_value (L003) | theorem all U32; stub checks four words and scalar <P |
| field::LPh_stubs::by_r | FIo_Native field.mul_by_r; LPh.Native.by_r_words (L005) | both words <P; helper private, callers stub the enclosing public op or use an in-core harness |
| field::LPh_stubs::wide | FIo_Native field.wide_exact.WideExact.mul; LPh.Native.wide_mul_words (L005) | every coordinate of both inputs <P; public WideExact constructors enforce this |

P=2147483647. cm/qm/wide result specs are natural-coordinate projections (`ZMod.val`) of the exact quadratic tower product, with canonical outputs. The Rust replacements expand that tower into Nat modular add/sub/product expressions. **The explicit equality of those expanded Rust expressions with the projection specifications is a remaining pairing stage until checked below; these stubs are not credited to any caller yet.** L001 independently transports the existing probe Nat word formulas to the SemanticCall extraction: m31_mul_value, cm31_mul_value, qm31_mul_value, mul_by_r_value. Those extraction carriers are not silently identified with FIo_Native.

## Dot raw boundary

Dot::push calls Q::raw, not the field operations above. The checked theorem AspisR1.FJf_RawReference.source gives the actual FIo_Native Q.raw successful result, in four explicit word expressions. A raw replacement must be paired with that theorem on exactly the same packed operands; field multiplication stubs alone do not replace this obligation. Native/model packed-array association remains distinct from the value theorem.
