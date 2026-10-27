import PoolS2_PdaLane
import PoolS2_PdaPrimitives
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PdaLaneAccepted
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_PdaSeeds

theorem accepted (ops : Ops) (program master key : Key) (lane bump : U8)
    (h : pair_forest.lane_address_matches ops program master lane bump key = ok (.Ok true)) :
    lane.val < 8 ∧ ops.create (laneCreate master lane bump) program = ok (.Ok key) := by
  have within := PoolS2_PdaLane.accepted_bound ops program master key lane bump true h
  rw [PoolS2_PdaLane.valid ops program master key lane bump within] at h
  have matched : registry.stored_bump_address_matches ops (laneCreate master lane bump) program key = ok true := by
    cases call : registry.stored_bump_address_matches ops (laneCreate master lane bump) program key with
    | fail e => simp [call] at h
    | div => simp [call] at h
    | ok result =>
      have yes : result = true := by simpa [call] using h
      simpa [yes] using call
  exact ⟨within,PoolS2_PdaPrimitives.accepted ops _ program key matched⟩

theorem accepted_iff (ops : Ops) (program master key : Key) (lane bump : U8) :
    pair_forest.lane_address_matches ops program master lane bump key = ok (.Ok true) ↔
      lane.val < 8 ∧ ops.create (laneCreate master lane bump) program = ok (.Ok key) := by
  refine ⟨accepted ops program master key lane bump,?_⟩
  rintro ⟨within,call⟩
  rw [PoolS2_PdaLane.valid ops program master key lane bump within]
  simp [PoolS2_PdaPrimitives.ready ops _ program key call]

theorem create_error (ops : Ops) (program master key : Key) (lane bump : U8) (e : PdaError)
    (within : lane.val < 8)
    (call : ops.create (laneCreate master lane bump) program = ok (.Err e)) :
    pair_forest.lane_address_matches ops program master lane bump key = ok (.Ok false) := by
  rw [PoolS2_PdaLane.valid ops program master key lane bump within]
  simp [PoolS2_PdaPrimitives.rejected ops _ program key e call]

#print axioms accepted
#print axioms accepted_iff
#print axioms create_error
end AspisR1.PoolS2_PdaLaneAccepted
end
