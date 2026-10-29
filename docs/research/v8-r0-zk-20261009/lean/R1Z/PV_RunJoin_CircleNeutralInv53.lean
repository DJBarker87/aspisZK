import R1Z.PV_RunJoin_CircleNeutralInvNonzero53
import R1Z.PV_RunJoin_CircleNeutralResult53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralInv53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53

theorem owned_zero : PV_RunJoin_CircleRawScalar52.field.M31.inv 0#u32 =
    (do massert false; ok 0#u32) := by
  unfold PV_RunJoin_CircleRawScalar52.field.M31.inv
  simp only [bne_self_eq_false,massert]
  rfl

theorem model_zero : PV_RunJoin_CircleR72Raw52.field.M31.inv 0#u32 =
    (do massert false; ok 0#u32) := by
  unfold PV_RunJoin_CircleR72Raw52.field.M31.inv
  simp only [bne_self_eq_false,massert]
  rfl

theorem complete (a : U32) (ha : Canon a) :
    Aligned Canon (PV_RunJoin_CircleRawScalar52.field.M31.inv a)
      (PV_RunJoin_CircleR72Raw52.field.M31.inv a) := by
  by_cases hz : a=0#u32
  · subst a
    rw [owned_zero,model_zero]
    exact ⟨rfl,by intro y hy; cases hy⟩
  · obtain ⟨y,hy,hy',hc⟩ := PV_RunJoin_CircleNeutralInvNonzero53.nonzero a ha
      (by simpa only [bne_iff_ne] using hz)
    exact returned Canon _ _ y hy hy' hc

#print axioms owned_zero
#print axioms model_zero
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralInv53
