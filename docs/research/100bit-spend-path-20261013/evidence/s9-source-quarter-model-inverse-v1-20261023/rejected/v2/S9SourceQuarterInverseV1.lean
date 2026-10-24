import S9ScalarActualPowerPolynomialV1
import CurrentWideMulM31V13
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace AspisR1S9SourceQuarterInverseV1
open AspisR1S9ProductionPairCutV1
abbrev M := AspisR1CurrentWide.Proof.MExact
abbrev E := AspisWideTower.WideExact

/-- Only the small Nat identity4*536870912=p+1 is evaluated; the modular
step explicitly uses that the modulus casts to zero. -/
theorem base_quarter_mul_four :
    R17CurrentM31Semantics.decode weights.QUARTER*(4 : M)=1 := by
  unfold weights.QUARTER R17CurrentM31Semantics.decode
  change (536870912 : ZMod 2147483647)*4=1
  have hn : (536870912 : Nat)*4=2147483647+1 := by omega
  have hc := congrArg (fun n : Nat => (n : ZMod 2147483647)) hn
  rw [Nat.cast_mul,Nat.cast_add,ZMod.natCast_self,Nat.cast_one,zero_add] at hc
  exact hc

private theorem mapped_inverse_four {A B : Type} [CommRing A] [Field B]
    (iota : A →+* B) (q : A) (h : q*(4 : A)=1) : iota q=(4 : B)⁻¹ := by
  have hb := congrArg iota h
  rw [map_mul,map_one,map_ofNat] at hb
  have hn : (4 : B)≠0 := by
    intro hz
    rw [hz,mul_zero] at hb
    exact zero_ne_one hb
  calc
    _ = iota q*((4 : B)*(4 : B)⁻¹) := by rw [mul_inv_cancel₀ hn,mul_one]
    _ = (iota q*(4 : B))*(4 : B)⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [hb,one_mul]

/-- Exact native source quarter through the existing embedding theorem.
All product/inverse manipulation happens on generic opaque variables above. -/
theorem source_quarter_eq_inverse_four :
    AspisR1S9ScalarActualPowerPolynomialV1.quarter=(4 : E)⁻¹ := by
  exact (AspisR1CurrentWide.Proof.wideScalarEmbedding_eq_algebraMap weights.QUARTER).trans
    (mapped_inverse_four (algebraMap M E)
      (R17CurrentM31Semantics.decode weights.QUARTER) base_quarter_mul_four)

#print axioms base_quarter_mul_four
#print axioms source_quarter_eq_inverse_four
end AspisR1S9SourceQuarterInverseV1
