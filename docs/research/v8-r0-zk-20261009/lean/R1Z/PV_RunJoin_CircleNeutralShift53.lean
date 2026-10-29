import R1Z.PV_RunJoin_CircleNeutralFold53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralShift53
open PV_RunJoin_CircleNeutralFold53

theorem shr31u (x : U64) : x >>> 31#u32 = ok (high x) := by rfl

theorem shr31i (x : U64) : x >>> 31#i32 = ok (high x) := by rfl

theorem low_mask (x : U64) :
    x &&& UScalar.cast .U64 PV_RunJoin_CircleR72Raw52.field.P = low x := by rfl

theorem fold_no_overflow (x : U64) :
    (low x).val+(high x).val < 18446744073709551616 := by
  rw [low_val,high_val]
  have hx := x.hBounds
  change x.val < 18446744073709551616 at hx
  omega

#print axioms shr31u
#print axioms shr31i
#print axioms low_mask
#print axioms fold_no_overflow
end R1Z.PV_RunJoin_CircleNeutralShift53
