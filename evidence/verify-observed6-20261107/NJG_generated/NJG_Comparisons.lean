import NJG_NativeCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJG_Comparisons
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
attribute [local instance] Classical.propDecidable

theorem qm31 (a b : aspis_core.field.QM31) :
 aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq a b=ok (decide (a=b)) := by
 cases a with | mk a0 a1=>
  cases b with | mk b0 b1=>
   cases a0 with | mk a00 a01=>
    cases a1 with | mk a10 a11=>
     cases b0 with | mk b00 b01=>
      cases b1 with | mk b10 b11=>
       by_cases h00:a00=b00 <;> by_cases h01:a01=b01 <;>
        by_cases h10:a10=b10 <;> by_cases h11:a11=b11 <;>
        simp_all [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
         aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
         aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]

theorem point (a b : aspis_core.circle.SecureCirclePoint) :
 FinishModel.pointEq a b=ok (decide (a=b)) := by
 cases a with | mk ax ay=>
  cases b with | mk bx by1=>
   by_cases hx:ax=bx <;> by_cases hy:ay=by1 <;> simp_all [FinishModel.pointEq,qm31]

#print axioms qm31
#print axioms point
end AspisR1.NJG_Comparisons
end
