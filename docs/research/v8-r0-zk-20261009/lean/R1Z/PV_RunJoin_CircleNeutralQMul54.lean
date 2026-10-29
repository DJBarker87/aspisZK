import R1Z.PV_RunJoin_R24Complete54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralQMul54
open PV_RunJoin_CircleNeutralShape53
abbrev Q := (U32 × U32) × (U32 × U32)
theorem complete (a b : Q) (ha : QC a) (hb : QC b) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.QM31.mul a b=ok y ∧
      PV_RunJoin_CircleR72Raw52.field.QM31.mul a b=ok y ∧ QC y := by
  obtain ⟨y,hy,ho,hc⟩ := PV_RunJoin_R24Complete54.complete a b ha hb
  refine ⟨y,ho,?_,hc⟩
  unfold PV_RunJoin_CircleR72Raw52.field.QM31.mul
  rw [hy,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralQMul54
