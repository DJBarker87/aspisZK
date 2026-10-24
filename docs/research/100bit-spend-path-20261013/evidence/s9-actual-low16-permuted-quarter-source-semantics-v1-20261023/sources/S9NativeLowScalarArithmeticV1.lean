import S9ActualPairMulM31CurrentV1
import S9NativeWideDecodedArithmeticV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9NativeLowScalarArithmeticV1
open AspisR1S9NativeWideDecodedArithmeticV1
abbrev E := AspisWideTower.WideExact
abbrev embed := AspisR1CurrentWide.Proof.wideScalarEmbedding

/-- Reuse existing full Result source maps and exact current-wide scaling.
No bound on the scalar is needed because source mul_m31 retains its %P. -/
theorem native_mul_m31_success (x out : W) (s : U32) (hx : Canonical x)
    (h : aspis_core.field.wide_exact.WideExact.mul_m31 x s=.ok out) :
    Canonical out ∧ decode out=decode x*embed s := by
  have hm := AspisR1S9ActualPairMulM31CurrentV1.actual_wide_mul_m31_maps_current x s
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toCurrent x) s=.ok (toCurrent out) := hm.symm
  exact AspisR1CurrentWide.Proof.wide_mul_m31_success (toCurrent x) (toCurrent out) s hx hc

theorem native_m31_mul_same (x y : U32) :
    aspis_core.field.M31.mul x y=AspisR1CurrentWide.field.M31.mul x y :=
  (AspisR1S9ActualPairMulM31CurrentV1.m31_mul_same x y).trans
    (AspisR1S9WideMulM31FullResultMapV1.m31_mul_eq_current x y)

/-- Exact source M31 square factor: reuse old M31 modular semantics and the
existing embedding homomorphism, without evaluating a concrete2^58 product. -/
theorem native_quarter_square_embedding (m : U32)
    (h : aspis_core.field.M31.mul weights.QUARTER weights.QUARTER=.ok m) :
    embed m=embed weights.QUARTER*embed weights.QUARTER := by
  rw [native_m31_mul_same,AspisR1CurrentWide.Proof.m31_mul_same] at h
  have he := R17CurrentM31Semantics.current_mul_decode weights.QUARTER weights.QUARTER m h
  change AspisR1CurrentWide.Proof.wideScalarEmbedding m =
    AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER *
      AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER
  simp only [AspisR1CurrentWide.Proof.wideScalarEmbedding_eq_algebraMap,he,map_mul]

#print axioms native_mul_m31_success
#print axioms native_m31_mul_same
#print axioms native_quarter_square_embedding
end AspisR1S9NativeLowScalarArithmeticV1
