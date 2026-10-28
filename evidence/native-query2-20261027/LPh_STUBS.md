# NBF field stub pairing

| Stub | Emitted theorem | Domain |
|---|---|---|
| NBF_query::NBF_m31 replacing aspis_core::field::M31::mul | AspisR1.LPh.Native.m31_value in evidence/leaf-p6-8-20261027/LPh_NativeScalar.lean, accepted L003 | Both U32 words<P. Returned kani::any U32 is assumed equal to ((x*y)%P) in Nat/u64 (product fits). Stub asserts domain; harness supplies canonical z. |

No other field stub is used. Pairing is reused, not re-proved. Port3 callback
installation is NBC_FieldOps in NBF_QueryDependencies.md and remains OPEN.
Other call-routing replacements are NBF_STUBS.md / NBF_QueryDependencies.md;
none without a paired bridge is credited as a callee pass.
