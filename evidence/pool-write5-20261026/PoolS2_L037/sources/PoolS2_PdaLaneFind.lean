import PoolS2_PdaLane
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PdaLaneFind
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_PdaSeeds

theorem valid (ops : Ops) (program master : Key) (lane : U8) (within : lane.val < 8) :
    pair_forest.pool_v1_pair_forest_lane_address ops program master lane = (do
      let pair ← ops.find (laneFind master lane) program
      ok (.Ok pair)) := by
  simp [pair_forest.pool_v1_pair_forest_lane_address,laneCount,within,laneSeed,lanePrefix,
    laneFind,asRef,keyBytes,oneByte,lift]

theorem invalid (ops : Ops) (program master : Key) (lane : U8) (outside : 8 ≤ lane.val) :
    pair_forest.pool_v1_pair_forest_lane_address ops program master lane =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidSeeds) := by
  simp [pair_forest.pool_v1_pair_forest_lane_address,laneCount,outside,lift]

theorem returned (ops : Ops) (program master key : Key) (lane bump : U8)
    (h : pair_forest.pool_v1_pair_forest_lane_address ops program master lane = ok (.Ok (key,bump))) :
    lane.val < 8 ∧ ops.find (laneFind master lane) program = ok (key,bump) := by
  have within : lane.val < 8 := by
    by_contra outside
    rw [invalid ops program master lane (by omega)] at h
    cases h
  rw [valid ops program master lane within] at h
  refine ⟨within,?_⟩
  cases call : ops.find (laneFind master lane) program with
  | fail e => simp [call] at h
  | div => simp [call] at h
  | ok pair =>
    have eq : pair = (key,bump) := by simpa [call] using h
    simpa [eq] using call

#print axioms valid
#print axioms invalid
#print axioms returned
end AspisR1.PoolS2_PdaLaneFind
end
