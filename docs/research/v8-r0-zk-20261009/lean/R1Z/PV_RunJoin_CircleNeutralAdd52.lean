import R1Z.PV_RunJoin_CircleNeutralScalar52
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleNeutralAdd52

def Canon (a : U32) : Prop := a.val < 2147483647

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    PV_RunJoin_CircleRawScalar52.field.M31.add a b = PV_RunJoin_CircleR72Raw52.field.M31.add a b := by
  have hab : a.val+b.val < 2^32 := by unfold Canon at ha hb;omega
  unfold PV_RunJoin_CircleRawScalar52.field.M31.add PV_RunJoin_CircleRawScalar52.field.ct.add
    PV_RunJoin_CircleR72Raw52.field.M31.add PV_RunJoin_CircleR72Raw52.field.P
  rw [PV_RunJoin_CircleNeutralScalar52.checked_add a b hab]
  simp only [lift,bind_tc_ok,PV_RunJoin_CircleNeutralScalar52.subtract_shape]
  simp only [core.num.U32.wrapping_add]
  by_cases h : U32.wrapping_add a b ≥ 2147483647#u32
  · simp only [h,if_pos]
    rw [PV_RunJoin_CircleNeutralScalar52.checked_sub _ _ h]
    simp only [bind_tc_ok]
  · simp only [h,if_neg,if_false]

theorem double (a : U32) (ha : Canon a) :
    PV_RunJoin_CircleRawScalar52.field.M31.double a = PV_RunJoin_CircleR72Raw52.field.M31.double a := by
  unfold PV_RunJoin_CircleRawScalar52.field.M31.double PV_RunJoin_CircleR72Raw52.field.M31.double
  exact complete a a ha ha

#print axioms Canon
#print axioms complete
#print axioms double
end R1Z.PV_RunJoin_CircleNeutralAdd52
