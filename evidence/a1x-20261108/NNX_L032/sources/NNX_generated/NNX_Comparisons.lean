import NNX_Masked
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Comparisons
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
attribute [local instance] Classical.propDecidable

theorem qm_eq (x y : aspis_core.field.QM31) :
 aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq x y = .ok (decide (x=y)) := by
 rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
 rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
 by_cases ha : a=e <;> by_cases hb : b=f <;> by_cases hc : c=g <;> by_cases hd : d=h <;>
  simp [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
   aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
   aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,ha,hb,hc,hd]

theorem qm_ne (x : aspis_core.field.QM31) :
 core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x x = .ok false := by
 simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
  aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,qm_eq,
  decide_true,bind_tc_ok,Bool.not_true]

theorem point (x y : aspis_core.circle.SecureCirclePoint) (different : x ≠ y) :
 FinishModel.pointEq x y = .ok false := by
 rw [FinishModel.pointEq,qm_eq,bind_tc_ok]
 by_cases hx : x.x=y.x
 · rw [if_pos (by simpa using hx),qm_eq]
   have hy : x.y ≠ y.y := by
    intro h
    exact different (by cases x;cases y;cases hx;cases h;rfl)
   simp only [hy,decide_false]
 · simp only [hx,decide_false,Bool.false_eq_true,if_false]

#print axioms qm_eq
#print axioms qm_ne
#print axioms point
end AspisR1.NNX_Comparisons
end
