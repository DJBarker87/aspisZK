import PoolS2_PdaSeeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PdaLane
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_PdaSeeds

theorem widen (lane : U8) :
    (core.convert.num.FromUsizeU8.from lane).val = lane.val := by scalar_tac

theorem valid (ops : Ops) (program master key : Key) (lane bump : U8)
    (within : lane.val < 8) :
    pair_forest.lane_address_matches ops program master lane bump key = do
      let matched ← registry.stored_bump_address_matches ops (laneCreate master lane bump) program key
      ok (.Ok matched) := by
  have guard : ¬ core.convert.num.FromUsizeU8.from lane >= 8#usize := by scalar_tac
  simp [pair_forest.lane_address_matches,laneCount,guard,laneSeed,lanePrefix,
    asRef,laneCreate,keyBytes,oneByte,lift]

theorem invalid (ops : Ops) (program master key : Key) (lane bump : U8)
    (outside : 8 ≤ lane.val) :
    pair_forest.lane_address_matches ops program master lane bump key =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidSeeds) := by
  have guard : core.convert.num.FromUsizeU8.from lane >= 8#usize := by scalar_tac
  simp [pair_forest.lane_address_matches,laneCount,guard,lift]

theorem accepted_bound (ops : Ops) (program master key : Key) (lane bump : U8) (matched : Bool)
    (h : pair_forest.lane_address_matches ops program master lane bump key = ok (.Ok matched)) :
    lane.val < 8 := by
  by_contra outside
  have ge : 8 ≤ lane.val := by omega
  rw [invalid ops program master key lane bump ge] at h
  cases h

#print axioms widen
#print axioms valid
#print axioms invalid
#print axioms accepted_bound
end AspisR1.PoolS2_PdaLane
end
