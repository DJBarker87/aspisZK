import R1Z.ProverCommitWideScalar48
import R1Z.ProverCommitM31Ops48
import Mathlib.Tactic.NormNum
/-! The shipped M31 quarter constant is exactly inverse four in the full tower. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitQuarter48
open ProverCommitWideOps48
open ProverCommitM31Ops48 (M)

theorem base_quarter : (536870912 : M)=(4 : M)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change (4*536870912 : ZMod 2147483647)=1
  rfl

theorem factor_quarter : ProverCommitWideScalar48.factor (536870912#u32)=(4 : Exact)⁻¹ := by
  change (algebraMap M Exact) (536870912 : M)=(4 : Exact)⁻¹
  rw [base_quarter,map_inv₀,map_ofNat]

#print axioms base_quarter
#print axioms factor_quarter
end R1Z.ProverCommitQuarter48
