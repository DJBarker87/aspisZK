import S9ScalarActualPowerPolynomialV1
import CurrentWideMulM31V13
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace AspisR1S9SourceQuarterInverseV1
open AspisR1S9ProductionPairCutV1
abbrev M := AspisR1CurrentWide.Proof.MExact
abbrev E := AspisWideTower.WideExact

/-- One small prime-field calculation:4*536870912=2147483647+1.
No tower recurrence or vector expansion is reduced. -/
theorem base_quarter_mul_four :
    R17CurrentM31Semantics.decode weights.QUARTER*(4 : M)=1 := by
  unfold weights.QUARTER R17CurrentM31Semantics.decode
  change (536870912 : ZMod 2147483647)*4=1
  norm_num

/-- The actual source quarter, through the existing exact embedding theorem,
is the inverse4 used by the model's radix-four dual fold. -/
theorem source_quarter_eq_inverse_four :
    AspisR1S9ScalarActualPowerPolynomialV1.quarter=(4 : E)⁻¹ := by
  have hb := congrArg (algebraMap M E) base_quarter_mul_four
  rw [map_mul,map_one] at hb
  have hfour : algebraMap M E (4 : M)=(4 : E) := map_ofNat _ 4
  rw [hfour] at hb
  have hq : AspisR1S9ScalarActualPowerPolynomialV1.quarter=
      algebraMap M E (R17CurrentM31Semantics.decode weights.QUARTER) :=
    AspisR1CurrentWide.Proof.wideScalarEmbedding_eq_algebraMap _
  rw [←hq] at hb
  have hn : (4 : E)≠0 := by
    intro hz
    rw [hz,mul_zero] at hb
    exact zero_ne_one hb
  calc
    _ = AspisR1S9ScalarActualPowerPolynomialV1.quarter*((4 : E)*(4 : E)⁻¹) := by
      rw [mul_inv_cancel₀ hn,mul_one]
    _ = (AspisR1S9ScalarActualPowerPolynomialV1.quarter*(4 : E))*(4 : E)⁻¹ :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [hb,one_mul]

#print axioms base_quarter_mul_four
#print axioms source_quarter_eq_inverse_four
end AspisR1S9SourceQuarterInverseV1
