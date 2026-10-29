import R1Z.PV_RDB2D_PV_B3P_ScheduleResult133
import R1Z.PV_RDB2D_PV_B3P_Sorted133
import R1Z.PV_RDB2D_PV_B3P_Canonical133
import R1Z.PV_RDB2D_PV_B3P_InputMembers133
import R1Z.PV_RDB2D_PV_B3P_OutputMembers133
import R1Z.PV_RDB2D_PV_B3P_Ordered133
namespace PV_B3P_SortedResult133
open PV_B3P_Schedule133 PV_B3P_Sorted133 PV_B3P_Canonical133
set_option autoImplicit false

attribute [local irreducible] legacyLinks forestLinks expected input

theorem canonical_eval : canonical input = expected := by
  apply canonical_eq _ _ PV_B3P_Ordered133.expected_ordered
  intro a
  exact ⟨fun h => PV_B3P_InputMembers133.subset h,
         fun h => PV_B3P_OutputMembers133.subset h⟩

def active : Except Error (List Nat) := do
  let schedule ← forest
  pure (canonical (endpoints schedule))

theorem complete_result : active = .ok expected := by
  unfold active
  rw [PV_B3P_ScheduleResult133.forest_success]
  change Except.ok (canonical (endpoints (forestLinks legacyLinks))) = _
  rw [PV_B3P_ForestValues133.forest_eval,endpoints_eval,canonical_eval]

theorem expected_length : expected.length = 214 := by
  unfold expected
  simp only [List.length_append,List.length_cons,List.length_nil]

theorem nonvacuity : ∃ rows, active = .ok rows ∧ rows.length = 214 :=
  ⟨expected,complete_result,expected_length⟩

#print axioms canonical_eval
#print axioms complete_result
#print axioms expected_length
#print axioms nonvacuity
end PV_B3P_SortedResult133
