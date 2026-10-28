# Field multiplication stub pairings

All replacements return `kani::any()` constrained by `kani::assume` to the
exact natural modular word specification. Each asserts its canonical input
domain. Shared `NBF_field::chosen` also assumes canonical output, a redundant
consequence of the named value theorem. No multiplication equivalence is
attempted in Kani. P=2147483647.

| Replacement | Existing emitted definition theorem | Domain / source callers |
|---|---|---|
| `NBF_query::NBF_m31` replacing `M31::mul` | `AspisR1.LPh.Native.m31_value`, `LPh_NativeScalar.lean`, accepted L003 | Both U32 words<P; exact `(x*y)%P`. Query node caller's z is canonical in its local harness. Full geometry-producer association remains NBC_Geometry. |
| `NBF_basis_mul` replacing `M31::mul` | Same `m31_value` | Selected basis word and node<P; other255 cells arbitrary U32. Native one-iteration frame K008; SAME returned basis canonicality is `NBF_BasisDomain.read_canonical`. |
| `NBF_field::m31` replacing `M31::mul` | Same `m31_value` | Both U32 words<P; ghost input/output observations only. Used by fold fragments and the native node cut. |
| `NBF_field::scalar` replacing `QM31::mul_m31` | `AspisR1.LPh.Native.qm_scalar_value`, `LPh_NativeScalar.lean`, accepted L003 | Four Q limbs and scalar<P; four exact modular products. Native `WideExact::mul_m31` remains actual and calls this twice. |
| `NBF_field::wide` replacing `WideExact::mul` | `AspisR1.LPh.Native.wide_mul_expanded`, `LPh_NativeWide.lean`, accepted L012 | All16 input limbs<P; eight exact natural Karatsuba-coordinate formulas and canonical output. |
| `NBF_field::qm31` replacing `QM31::mul` | `AspisR1.LPh.Native.qm_mul_expanded`, `LPh_ExpandedQ.lean`, accepted L007 | All8 input limbs<P; four exact natural Karatsuba-coordinate formulas. Native `WideExact::mul_qm31` remains actual and invokes this twice before the old-power/rho call. |

The shared field specification is a prefix-renamed copy of
`evidence/leaf-p6-8-20261027/LPh_field_stubs.patch`, with observations and the
redundant output-domain assumptions. The source expressions and word order are
unchanged. These are reused emitted value theorems, not freshly re-proved field
lemmas. The exact direct Port3/field carrier and callback installation is the
explicit NBC_FieldOps dependency in NBF_QueryDependencies.md, still OPEN.

No source/caller is credited for an unpaired replacement. Other non-field
routing replacements and their OPEN semantic obligations are in NBF_STUBS.md.
K019/K021 timeouts and any other failed gate retain their source/metrics and
receive no proof credit; a natural-spec stub is not itself a passed caller.
