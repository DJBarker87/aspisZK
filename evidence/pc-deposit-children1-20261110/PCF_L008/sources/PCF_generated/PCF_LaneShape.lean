import PCF_LaneRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_LaneShape

def canonical (a b c d e f g h : U32) : Prop :=
  a < 2147483647#u32 ∧ b < 2147483647#u32 ∧ c < 2147483647#u32 ∧ d < 2147483647#u32 ∧
  e < 2147483647#u32 ∧ f < 2147483647#u32 ∧ g < 2147483647#u32 ∧ h < 2147483647#u32

def lowLane (a : U32) : U16 := UScalar.cast .U16 ((UScalar.cast .U8 a) &&& 7#u8)

theorem complete (a b c d e f g h : U32) :
    PCF_LaneRef.lane_reference a b c d e f g h =
      ok (if canonical a b c d e f g h then lowLane a else 256#u16) := by
  simp only [PCF_LaneRef.lane_reference, lift, bind_tc_ok, canonical, lowLane]
  split_ifs <;> simp_all <;> scalar_tac

#print axioms complete
end PCF_LaneShape
