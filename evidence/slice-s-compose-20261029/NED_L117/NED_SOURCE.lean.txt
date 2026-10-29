import NED_LateEncodingConstants
set_option autoImplicit false
namespace NED_LateCarrierFields
open NED_LateCarriers NED_ReconstructCarriers

theorem live (s : TLate) : (toRawLate s).live_snapshot = toRawSnapshot s.live_snapshot := by rfl
theorem after (s : TLate) : (toRawLate s).candidate_afterstate = toRawAfter s.candidate_afterstate := by rfl
theorem live_index (s : TSnapshot) : (toRawSnapshot s).next_pair_index = s.next_pair_index := by rfl
theorem after_index (s : TAfter) : (toRawAfter s).next_pair_index = s.next_pair_index := by rfl
theorem live_frontier (s : TSnapshot) : (toRawSnapshot s).frontier = s.frontier := by rfl
theorem after_frontier (s : TAfter) : (toRawAfter s).next_frontier = s.next_frontier := by rfl
theorem common_late (s : Common) : (NED_ReconstructCarriers.toRawCommon s).lane_transition = toRawLate s.lane_transition := by rfl
theorem common_anchor (s : Common) : (NED_ReconstructCarriers.toRawCommon s).historical_global_anchor = s.historical_global_anchor := by rfl

#print axioms live
#print axioms after
#print axioms live_index
#print axioms after_index
#print axioms live_frontier
#print axioms after_frontier
#print axioms common_late
#print axioms common_anchor
end NED_LateCarrierFields
