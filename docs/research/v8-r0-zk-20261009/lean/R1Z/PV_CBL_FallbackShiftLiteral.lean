import R1Z.PV_CBL_FallbackScalar
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackShiftLiteral
/-- Explicit signed-to-unsigned literal port in the owned fallback schedule.
Both Rust shift operands denote the same nonnegative count below the width. -/
theorem same_value : (10#i32).val = Int.ofNat (10#u32).val := rfl
theorem same_count : Int.toNat (10#i32).val % 32 = (10#u32).val % 32 := rfl
theorem in_width : (10#u32).val < 32 := by decide
#print axioms same_value
#print axioms same_count
#print axioms in_width
end R1Z.PV_CBL_FallbackShiftLiteral
