import R1Z.PV_RunJoin_CircleNeutralBase52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralZeroResult53
theorem ctotal (a : U32 × U32) : ∃ z,
    PV_RunJoin_CircleRawTower52.field.CM31.is_zero a = ok z ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.is_zero a = ok z := by
  have hz : PV_RunJoin_CircleRawTower52.field.CM31.is_zero a =
      ok (decide (a.1=0#u32) && decide (a.2=0#u32)) := rfl
  exact ⟨_,hz,(PV_RunJoin_CircleNeutralBase52.czero a).symm.trans hz⟩

theorem qtotal (a : (U32 × U32) × (U32 × U32)) : ∃ z,
    PV_RunJoin_CircleRawTower52.field.QM31.is_zero a = ok z ∧
      PV_RunJoin_CircleR72Raw52.field.QM31.is_zero a = ok z := by
  obtain ⟨b,hb,hb'⟩ := ctotal a.1
  obtain ⟨c,hc,hc'⟩ := ctotal a.2
  have hz : PV_RunJoin_CircleRawTower52.field.QM31.is_zero a = ok (b && c) := by
    unfold PV_RunJoin_CircleRawTower52.field.QM31.is_zero
    simp only [hb,hc,bind_tc_ok]
  exact ⟨_,hz,(PV_RunJoin_CircleNeutralBase52.qzero a).symm.trans hz⟩

#print axioms ctotal
#print axioms qtotal
end R1Z.PV_RunJoin_CircleNeutralZeroResult53
