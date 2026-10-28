# NBF field stub pairing

| Stub | Emitted theorem | Domain |
|---|---|---|
| NBF_query::NBF_m31 replacing aspis_core::field::M31::mul | AspisR1.LPh.Native.m31_value in evidence/leaf-p6-8-20261027/LPh_NativeScalar.lean, accepted L003 | Both U32 words<P. Returned kani::any U32 is assumed equal to ((x*y)%P) in Nat/u64 (product fits). Stub asserts domain; harness supplies canonical z. |

No other field stub is used. Pairing is reused, not re-proved. Port3 callback
installation is NBC_FieldOps in NBF_QueryDependencies.md and remains OPEN.
Other call-routing replacements are NBF_STUBS.md / NBF_QueryDependencies.md;
none without a paired bridge is credited as a callee pass.

| NBF_harness::NBF_basis_mul replacing M31::mul in one basis-loop iteration | Same AspisR1.LPh.Native.m31_value, and S7JoinBasisCanonical.wordMul_canonical for next-domain propagation | Selected basis word<P and node<P. Stub asserts both, returns any U32 constrained to exact natural modular product. Other255 cells arbitrary U32; no global canonicality is assumed by the native step. |
