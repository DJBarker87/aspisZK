import NNG_LegacyCalls136
set_option autoImplicit false
namespace AspisR1.NNG_LegacyEquality136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Transport

theorem cm (x y : aspis_core.field.CM31) :
 AspisR1PublicPreparation.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq (toT0 x) (toT0 y)=.ok (decide (x=y)) := by
 rcases x with ⟨a,b⟩
 rcases y with ⟨c,d⟩
 by_cases ha : a=c <;> by_cases hb : b=d <;>
  simp [AspisR1PublicPreparation.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,toT0,ha,hb]

theorem qm (x y : aspis_core.field.QM31) :
 AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq (toT1 x) (toT1 y)=.ok (decide (x=y)) := by
 rcases x with ⟨x0,x1⟩
 rcases y with ⟨y0,y1⟩
 simp only [AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,toT1,cm,bind_tc_ok]
 by_cases h0 : x0=y0 <;> by_cases h1 : x1=y1 <;> simp [h0,h1]

theorem point (x y : aspis_core.circle.SecureCirclePoint) :
 AspisR1PublicPreparation.FinishModel.pointEq (toT2 x) (toT2 y)=.ok (decide (x=y)) := by
 rcases x with ⟨x0,x1⟩
 rcases y with ⟨y0,y1⟩
 simp only [AspisR1PublicPreparation.FinishModel.pointEq,toT2,qm,bind_tc_ok]
 by_cases h0 : x0=y0 <;> by_cases h1 : x1=y1 <;> simp [h0,h1]

theorem ne (x y : aspis_core.field.QM31) :
 core.cmp.PartialEq.ne.default AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
   (toT1 x) (toT1 y)=.ok (decide (x≠y)) := by
 unfold core.cmp.PartialEq.ne.default
 rw [qm,bind_tc_ok]
 by_cases h : x=y <;> simp [h]
#print axioms cm
#print axioms qm
#print axioms point
#print axioms ne
end AspisR1.NNG_LegacyEquality136
