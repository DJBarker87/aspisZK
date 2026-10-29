import PV_B3P_Operations12227
namespace PV_B3P_Caller15227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- The only reachable dot call uses two seven-element arrays. Its original
length assertion therefore holds and its <=4 fast branch is not taken. -/
theorem dot7_source_entry15 (weights : Array aspis_core.field.QM31 7#usize)
    (values : Array aspis_core.field.M31 7#usize) :
    weights.val.length = values.val.length ∧ ¬ weights.val.length ≤ 4 := by
  rw [weights.property,values.property]
  decide

theorem dot7_block_indices15 (start index : Nat) (block : start = 0 ∨ start = 4)
    (member : start ≤ index ∧ index < min (start+4) 7) :
    index < 7 ∧ index-start < 4 := by omega

/-- The two source chunks preserve term order and do not pad the final block. -/
theorem dot7_ordered_partition15 : List.range' 0 4 ++ List.range' 4 3 = List.range' 0 7 := by
  decide
#print axioms dot7_source_entry15
#print axioms dot7_block_indices15
#print axioms dot7_ordered_partition15
end PV_B3P_Caller15227
