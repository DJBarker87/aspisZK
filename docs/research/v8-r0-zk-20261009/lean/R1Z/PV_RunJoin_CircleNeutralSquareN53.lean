import R1Z.PV_RunJoin_CircleNeutralSquareLoop53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralSquareN53
open PV_RunJoin_CircleNeutralShape53

theorem complete (a : U32) (ha : Canon a) (count : Usize) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.square_n a count = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.square_n a count = ok y ∧ Canon y := by
  obtain ⟨y,hy,hy',hc⟩ := PV_RunJoin_CircleNeutralFinite53.total count.val a ha
  refine ⟨y,?_,?_,hc⟩
  · unfold PV_RunJoin_CircleRawScalar52.field.square_n
    rw [PV_RunJoin_CircleNeutralSquareLoop53.owned count.val _ a (by simp)]
    exact hy
  · unfold PV_RunJoin_CircleR72Raw52.field.square_n
    rw [PV_RunJoin_CircleNeutralSquareLoop53.model count.val _ a (by simp)]
    exact hy'

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralSquareN53
