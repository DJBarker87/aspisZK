import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace AspisS1FirstErrorPartition

/-- Proof indices for the native claim's six points and 29 columns. This is
not a replacement runtime carrier or an original-source evaluator. -/
theorem rejection_cover (ordinal : Nat) (bound : ordinal<174) :
    ∃ point column : Nat,point<6 ∧ column<29 ∧ ordinal=29*point+column := by
  refine ⟨ordinal/29,ordinal%29,?_,?_,?_⟩ <;> omega

theorem full_cover (ordinal : Nat) (bound : ordinal≤174) :
    ordinal=174 ∨ ∃ point column : Nat,point<6 ∧ column<29 ∧ ordinal=29*point+column := by
  by_cases rejected : ordinal<174
  · exact Or.inr (rejection_cover ordinal rejected)
  · exact Or.inl (by omega)

theorem index_bounds (point column : Nat) (p : point<6) (c : column<29) :
    29*point+column<174 ∧ 29*point+column+1≤174 ∧
    (29*point+column)/29=point ∧ (29*point+column)%29=column := by omega

def fieldCount (ordinal : Nat) : Nat := if ordinal<145 then 0 else ordinal-144

theorem failed_field_count (point column : Nat) (p : point<6) (c : column<29) :
    fieldCount (29*point+column)=(if point=5 then column+1 else 0) := by
  unfold fieldCount
  split <;> split <;> omega

theorem counter_ranges (ordinal : Nat) (bound : ordinal<174) :
    ordinal+1≤174 ∧ ordinal/29<6 ∧ fieldCount ordinal≤29 := by
  unfold fieldCount
  split <;> omega

#print axioms rejection_cover
#print axioms full_cover
#print axioms index_bounds
#print axioms failed_field_count
#print axioms counter_ranges
end AspisS1FirstErrorPartition
