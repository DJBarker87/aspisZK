# NBF field stub pairing

| Stub | Emitted theorem | Domain |
|---|---|---|
| NBF_query::NBF_m31 replacing aspis_core::field::M31::mul | AspisR1.LPh.Native.m31_value in evidence/leaf-p6-8-20261027/LPh_NativeScalar.lean, accepted L003 | Both U32 words<P. Returned kani::any U32 is assumed equal to ((x*y)%P) in Nat/u64 (product fits). Stub asserts domain; harness supplies canonical z. |

No other field stub is used. Pairing is reused, not re-proved. Port3 callback
installation is NBC_FieldOps in NBF_QueryDependencies.md and remains OPEN.
Other call-routing replacements are NBF_STUBS.md / NBF_QueryDependencies.md;
none without a paired bridge is credited as a callee pass.

| NBF_harness::NBF_basis_mul replacing M31::mul in one basis-loop iteration | Same AspisR1.LPh.Native.m31_value, and S7JoinBasisCanonical.wordMul_canonical for next-domain propagation | Selected basis word<P and node<P. Stub asserts both, returns any U32 constrained to exact natural modular product. Other255 cells arbitrary U32; no global canonicality is assumed by the native step. |

## Fold caller arithmetic (NBF_field)

These are prefix-renamed copies of LPh_field_stubs.patch's natural specs, plus
read-only call observations and redundant canonical-output assumptions implied
by the paired theorems. No multiplication equivalence is attempted in Kani.

| Stub | Existing named emitted discharge | Domain |
|---|---|---|
| NBF_field::m31 | AspisR1.LPh.Native.m31_value | Both U32<P; returns exact modular natural product and canonical output. |
| NBF_field::scalar for QM31::mul_m31 | AspisR1.LPh.Native.qm_scalar_value | Four Q limbs and base scalar<P; returns each exact modular product. The native WideExact::mul_m31 wrapper is left actual and calls this twice. |
| NBF_field::wide | AspisR1.LPh.Native.wide_mul_expanded (LPh_NativeWide, accepted L012) | All16 input limbs<P; eight exact natural Karatsuba-coordinate formulas and canonical outputs. |

The stubs assert every input domain. Fold harnesses start with arbitrary
canonical E inputs and inverse words, and native add/sub propagates canonical
intermediates. Domain assertions remain checked at every reached field call.
The source/cohort op16/op17 installation is still a separate named dependency;
a field-stub routing pass alone does not close that installation.
