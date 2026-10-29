import R1Z.PV_RunJoin_CircleNeutralCast53
import R1Z.PV_RunJoin_CircleNeutralChecked64_53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR23_53
open PV_RunJoin_CircleNeutralCast53

theorem complete (a b : U64) :
    PV_RunJoin_CircleR72Raw52.field.r23_product_u32_bounded a b = a*b := by
  unfold PV_RunJoin_CircleR72Raw52.field.r23_product_u32_bounded
  simp only [lift,bind_tc_ok]
  by_cases ha : a ≤ core.convert.num.FromU64U32.from core.num.U32.MAX
  · rw [if_pos ha]
    by_cases hb : b ≤ core.convert.num.FromU64U32.from core.num.U32.MAX
    · rw [if_pos hb]
      change UScalar.cast .U64 (UScalar.cast .U32 a) * UScalar.cast .U64 (UScalar.cast .U32 b) = a*b
      rw [up_down a (by change a.val ≤ 4294967295 at ha;omega),
        up_down b (by change b.val ≤ 4294967295 at hb;omega)]
    · rw [if_neg hb]
  · rw [if_neg ha]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralR23_53
