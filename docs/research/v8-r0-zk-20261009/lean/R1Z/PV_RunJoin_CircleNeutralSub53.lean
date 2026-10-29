import R1Z.PV_RunJoin_CircleNeutralSubtract53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralSub53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralWord53

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.sub a b = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.M31.sub a b = ok y ∧ Canon y := by
  have ha' : a.val < 2147483647 := ha
  have hb' : b.val < 2147483647 := hb
  have hv : (U32.wrapping_add a 2147483647#u32).val = a.val+2147483647 :=
    add32 _ _ (by change a.val+2147483647 < 4294967296; omega)
  have hle : b.val ≤ (U32.wrapping_add a 2147483647#u32).val := by rw [hv]; omega
  have hv1 : (U32.wrapping_sub (U32.wrapping_add a 2147483647#u32) b).val < 4294967294 := by
    rw [sub32 _ _ hle,hv]; omega
  obtain ⟨y,hy,hcanonical⟩ := PV_RunJoin_CircleNeutralSubtract53.total _ hv1
  have hsource : PV_RunJoin_CircleRawScalar52.field.M31.sub a b = ok y := by
    unfold PV_RunJoin_CircleRawScalar52.field.M31.sub PV_RunJoin_CircleRawScalar52.field.ct.sub
      PV_RunJoin_CircleRawScalar52.field.P
    simp only [lift,bind_tc_ok,hy]
  refine ⟨y,hsource,?_,hcanonical⟩
  unfold PV_RunJoin_CircleR72Raw52.field.M31.sub PV_RunJoin_CircleR72Raw52.field.P
  rw [PV_RunJoin_CircleNeutralScalar52.checked_add _ _ (by change a.val+2147483647 < 2^32;omega)]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_CircleNeutralScalar52.checked_sub _ _ hle]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_CircleNeutralSubtract53.source] at hy
  unfold PV_RunJoin_CircleNeutralSubtract53.output at hy
  split <;> simp_all only [bind_tc_ok]
  all_goals rw [PV_RunJoin_CircleNeutralScalar52.checked_sub _ _ (by assumption)]
  all_goals simp_all only [bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralSub53
