import NNX_Masked
import FIr_FinishComparison
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Comparisons
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem qm_ne (x : aspis_core.field.QM31) :
 core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x x = .ok false := by
 simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
  aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,FIr_FinishComparison.qm_eq_source,
  decide_true,bind_tc_ok,Bool.not_true]

theorem point (x y : aspis_core.circle.SecureCirclePoint) (different : x ≠ y) :
 FinishModel.pointEq x y = .ok false := by
 rw [FinishModel.pointEq,FIr_FinishComparison.qm_eq_source,bind_tc_ok]
 by_cases hx : x.x=y.x
 · rw [if_pos (by simpa using hx),FIr_FinishComparison.qm_eq_source]
   have hy : x.y ≠ y.y := by
    intro h
    exact different (by cases x;cases y;cases hx;cases h;rfl)
   simp only [hy,decide_false]
 · simp only [hx,decide_false,Bool.false_eq_true,if_false]

#print axioms qm_ne
#print axioms point
end AspisR1.NNX_Comparisons
end
