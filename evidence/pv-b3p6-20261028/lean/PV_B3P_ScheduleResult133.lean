import PV_B3P_EndpointResult133
import PV_B3P_LegacyCapacity133
import PV_B3P_ForestCapacity133
namespace PV_B3P_ScheduleResult133
open PV_B3P_Schedule133 PV_B3P_EndpointResult133
set_option autoImplicit false

theorem legacy_length : legacyLinks.length = 127 := by
  rw [PV_B3P_LegacyValues133.legacy_eval]
  rfl

theorem legacy_capacity : checkEndpoints legacyLinks [] [] = .ok () := by
  rw [PV_B3P_LegacyValues133.legacy_eval]
  exact PV_B3P_LegacyCapacity133.success

theorem legacy_success : legacy = .ok legacyLinks :=
  checked_success _ _ legacy_length legacy_capacity

theorem forest_length : (forestLinks legacyLinks).length = 136 := by
  rw [PV_B3P_ForestValues133.forest_eval]
  rfl

theorem forest_capacity : checkEndpoints (forestLinks legacyLinks) [] [] = .ok () := by
  rw [PV_B3P_ForestValues133.forest_eval]
  exact PV_B3P_ForestCapacity133.success

attribute [local irreducible] legacyLinks forestLinks checked

theorem forest_success : forest = .ok (forestLinks legacyLinks) := by
  rw [forest,legacy_success]
  exact checked_success _ _ forest_length forest_capacity

theorem all_endpoints_in_bounds : ∀ x ∈ forestLinks legacyLinks,
    x.producer < 1024 ∧ x.consumer < 1024 :=
  check_bounds _ _ _ forest_capacity

#print axioms legacy_length
#print axioms legacy_capacity
#print axioms legacy_success
#print axioms forest_length
#print axioms forest_capacity
#print axioms forest_success
#print axioms all_endpoints_in_bounds
end PV_B3P_ScheduleResult133
