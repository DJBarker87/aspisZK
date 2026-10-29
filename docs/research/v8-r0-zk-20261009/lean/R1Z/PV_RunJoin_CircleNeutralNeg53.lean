import R1Z.PV_RunJoin_CircleNeutralSubtract53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralNeg53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralWord53

theorem complete (a : U32) (ha : Canon a) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.neg a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.M31.neg a = ok y ∧ Canon y := by
  by_cases hz : a = 0#u32
  · subst a
    exact ⟨0#u32,rfl,rfl,zero⟩
  · have hp : a.val ≤ (2147483647#u32).val := by change a.val ≤ 2147483647; exact Nat.le_of_lt ha
    have hv : (U32.wrapping_sub 2147483647#u32 a).val = 2147483647-a.val := sub32 _ _ hp
    refine ⟨U32.wrapping_sub 2147483647#u32 a,?_,?_,?_⟩
    · have hbool : (a != 0#u32) = true := by simp [hz]
      unfold PV_RunJoin_CircleRawScalar52.field.M31.neg PV_RunJoin_CircleRawScalar52.field.ct.neg
      simp only [hbool,lift,bind_tc_ok,PV_RunJoin_CircleRawScalar52.field.P]
      change ok (⟨(U32.wrapping_sub 2147483647#u32 a).bv &&& (-1#32)⟩ : U32) = _
      simp only [BitVec.and_neg_one]
    · unfold PV_RunJoin_CircleR72Raw52.field.M31.neg PV_RunJoin_CircleR72Raw52.field.P
      rw [if_neg hz,PV_RunJoin_CircleNeutralScalar52.checked_sub _ _ hp,bind_tc_ok]
    · unfold Canon
      rw [hv]
      have hne : a.val ≠ 0 := by intro h; apply hz; apply UScalar.eq_of_val_eq; exact h
      omega

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralNeg53
