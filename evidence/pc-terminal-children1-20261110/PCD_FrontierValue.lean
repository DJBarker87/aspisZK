import PCD_ArrayValue
set_option autoImplicit false
namespace PCD_FrontierValue
open Aeneas Aeneas.Std

def test (next : U64) (level : U32) (node empty : Array U32 8#usize) : Bool :=
  if level >= 20#u32 then false
  else if (U64.wrapping_shr next level &&& 1#u64) != 0#u64 then true
  else decide (node.val = empty.val)

theorem reference_exact (next : U64) (level : U32)
    (node empty : Array U32 8#usize) :
    PCD_LaneRef.frontier_step next level node empty = Result.ok (test next level node empty) := by
  unfold PCD_LaneRef.frontier_step test
  split
  · rfl
  · simp only [lift, bind_tc_ok]
    split
    · rfl
    · exact PCD_ArrayValue.array_equal node empty
#print axioms reference_exact
end PCD_FrontierValue
