import R1Z.ProverCommitShift49
/-! Algebraic reasons the final shift preserves its boundary guard and changes
only the terminal contribution. These laws do not supply source inversion or
source oracle/model correspondence. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitShiftGuards49
open Polynomial

variable {K : Type} [Field K]

theorem boundary_preserved (p : K[X]) (c half : K) (hh : half+half=1) :
    (p+C c*(X-C half)).eval 0+(p+C c*(X-C half)).eval 1=p.eval 0+p.eval 1 := by
  simp only [eval_add,eval_mul,eval_sub,eval_X,eval_C]
  calc
    _=p.eval 0+p.eval 1+c*(1-(half+half)) := by ring
    _=p.eval 0+p.eval 1 := by rw [hh];ring

theorem terminal_adjustment (p : K[X]) (original eta0 mask a half : K)
    (hne : a≠half) (terminal : p.eval a=mask+eta0) :
    (p+C ((original-eta0)*(a-half)⁻¹)*(X-C half)).eval a=mask+original := by
  simp only [eval_add,eval_mul,eval_sub,eval_X,eval_C]
  rw [terminal,mul_assoc,inv_mul_cancel₀ (sub_ne_zero.mpr hne),mul_one]
  ring

#print axioms boundary_preserved
#print axioms terminal_adjustment
end R1Z.ProverCommitShiftGuards49
