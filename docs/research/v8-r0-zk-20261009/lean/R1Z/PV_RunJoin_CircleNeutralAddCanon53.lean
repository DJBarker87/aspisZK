import R1Z.PV_RunJoin_CircleNeutralSubtract53
import R1Z.PV_RunJoin_CircleNeutralAdd52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralAddCanon53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralWord53

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.add a b = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.M31.add a b = ok y ∧ Canon y := by
  have hab : a.val+b.val < 4294967294 := by unfold Canon at ha hb; omega
  have hv : (U32.wrapping_add a b).val < 4294967294 := by
    rw [add32 _ _ (by omega)]
    exact hab
  obtain ⟨y,hy,hcanonical⟩ := PV_RunJoin_CircleNeutralSubtract53.total _ hv
  have hsource : PV_RunJoin_CircleRawScalar52.field.M31.add a b = ok y := by
    unfold PV_RunJoin_CircleRawScalar52.field.M31.add PV_RunJoin_CircleRawScalar52.field.ct.add
    simp only [lift,bind_tc_ok,hy]
  refine ⟨y,hsource,?_,hcanonical⟩
  rw [← PV_RunJoin_CircleNeutralAdd52.complete a b ha hb]
  exact hsource

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralAddCanon53
