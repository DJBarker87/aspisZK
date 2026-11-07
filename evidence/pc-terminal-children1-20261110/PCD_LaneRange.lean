import PCD_LaneModel
set_option autoImplicit false
namespace PCD_LaneModel
open Aeneas Aeneas.Std PCD PCD_LaneRef PCD_LaneLoop
/-- The complete source range is a full-value subset, not an ABI quotient:
Ok(the determined Lane) or Custom(0x41532003), with no String-bearing error,
allocation or source abort. Native panic/bounds checks are separate receipts. -/
theorem outcome_range (lane : Lane) (after : After) :
    source lane after = .ok (PCD_LaneValue.candidate lane after) ∨
    source lane after = .error (.custom 0x41532003) := by
  classical
  suffices specification lane after = .ok (PCD_LaneValue.candidate lane after) ∨
      specification lane after = .error (.custom 0x41532003) by
    simpa only [result] using this
  unfold specification
  by_cases checked : U64.checked_add lane.tree.next_leaf_index 1#u64 = some after.next_pair_index
  · rw [if_pos checked]
    by_cases all : good (tests after) 0 20
    · rw [if_pos all]; exact Or.inl rfl
    · rw [if_neg all]; exact Or.inr rfl
  · rw [if_neg checked]; exact Or.inr rfl
#print axioms outcome_range
end PCD_LaneModel
