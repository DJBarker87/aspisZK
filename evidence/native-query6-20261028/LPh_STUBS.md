# NCG opaque log substitutions

Inherited NBZ/NBW/NBO/NBF/NBB/LPh pairings are reused unchanged. KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; payload ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.

| Stub | Named emitted Lean value theorem | Domain / use |
|---|---|---|
| NCG_add_spec, opaque whole add/product result | NBB_Arithmetic.add; NCG_CallLog.substitute/base_substitution consumes exact call association | coefficient/scalar<P; old<2^34+phase*(P-1)^2; phase<4. Stub asserts input domain, logs old/coefficient/scalar/result, imposes NO result constraint. Structural proof only; semantic substitution remains explicit. |
| NCG_wide_opaque → WideExact::mul | AspisR1.LPh.Native.wide_mul_expanded; NBZ_Wide.product_total on coherent probe | all16 input limbs<P; output is arbitrary canonical WideExact, with no product relation. Canonical carrier bounds alone are used; NBZ_Wide/NBZ_Folds supply emitted output totality/domain. Caller constructs canonical inputs and checks logged operands/order. |

Kani does not prove field multiplication. Neither an opaque structural pass nor the explicit NCG semantic substitution template installs the native/emitted association by itself.
| NCG_scalar_opaque → QM31::mul_m31 | AspisR1.LPh.Native.qm_scalar_value | four QM limbs and scalar<P; arbitrary canonical four-word reply; no product constraint; callers assert domain and log both Wide halves separately. |
| NCG_m31_opaque → M31::mul | AspisR1.LPh.Native.m31_value | both limbs<P; arbitrary canonical reply; no product constraint; input operand/order checked. |
