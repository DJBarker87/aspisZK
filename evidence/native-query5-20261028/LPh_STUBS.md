# NBZ field and operation pairings

All inherited pairings in native-query4-20261028/LPh_STUBS.md and native-query2-20261027/LPh_STUBS.md are imported unchanged. Native multiplication is never verified in Kani.

| Stub | Paired named Lean theorem | Domain and exact value |
|---|---|---|
| NBZ_steps::NBZ_field::wide → WideExact::mul | AspisR1.LPh.Native.wide_mul_expanded, accepted LPh L012, inherited NBF pairing | All 16 input limbs<P; any eight-word reply constrained to exact natural Karatsuba formulas; output canonicality redundant. The Horner-step harness constructs canonical alpha/previous; later fold-stage domains are derived by NBZ_Folds/NBZ_Wide, pending native installation. |
| NBZ_field::m31 / scalar / qm31 / cm31 / by_r (included unchanged, not all reached) | m31_value / qm_scalar_value / qm_mul_expanded / cm_mul_expanded / by_r_expanded from inherited LPh table | Same exact canonical natural specifications as NBF's field module. No new theorem or broader domain claimed. |
| NBZ_steps::NBZ_reducer → M31::reduce_u64 | S8OwnedP6ValueModel.reducer_total/value_total_model; NBO_Enumerate.from_cursor | Routing-only overapproximation of four canonical replies, exact input order checked; no native reducer value credit beyond inherited Lean semantics. Arbitrary U64 input. The complete finish native association remains open until caller/reducer installation composes. |
| Exact KMX payload | KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame/append_spec/realloc_prefix | Exact upstream patch and stub hashes in NBZ_IMPORTS.json. Each positive copy-dependent gate also needs its own failing matched negative control. |

NBZ_Wide.product_total and NBZ_Folds domain theorems use the coherent probe carrier. They do not reattribute historical emitted FIo proofs to a different source or install NBC_FieldOps.

| NBZ_dots/NBZ_rescue::NBZ_add_spec → factored integer add/product expression | NBB_Arithmetic.add, on the exact S7OwnedP6Scalar.residue_scalar_owned emitted fragment with flush=false; caller phase supplied by NBZ_DotPhase.caller | old <2^34+phase*(P-1)^2, phase<4, both U32 inputs<P. Returns any U64 constrained in U128 arithmetic to old+coefficient*scalar. This is the same integer expression as the frozen base-prefix statement. K065 timed out; no product equivalence is claimed from Kani. |
| NBZ_dots::NBZ_reduce_spec → M31::reduce_u64 | S8OwnedP6ValueModel.reducer_total/value_total_model; NBB_Arithmetic.fold for the prior fold | All U64; any U32 constrained exactly to x%P, hence canonical. Actual eight returned words and callback order are checked. |
