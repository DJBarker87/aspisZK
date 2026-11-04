import NEU_BoxModel
import NDM_CohortReconstruction
set_option autoImplicit false
noncomputable section
namespace NEU_ReconstructCore
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1
abbrev Request := pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1

def common (a : Auth) (c : Candidate) : Common :=
  { master_account := a.master_account, checkpoint_account := a.checkpoint_account,
    selected_lane_account := a.selected_lane_account, output_lane := a.selected_lane.lane_id,
    checkpoint_sequence := a.checkpoint.checkpoint_sequence,
    historical_global_anchor := a.checkpoint.global_root,
    lane_transition := {live_snapshot := a.live_snapshot, candidate_afterstate := c} }

theorem common_result (a : Auth) (c : Candidate) :
    r1_pool_adapter.asq8_common a c = ok (common a c) := rfl

def run {State : Type} (request : Request) (a : Auth) (c : Candidate) (state : State) :=
  if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
    if a.master.identity.asset_id=NDM_CohortReconstruction.requested request then
      match request.public with
      | .PrivateTransfer p => NEU_BoxModel.run (.PrivateTransfer (common a c) p) state
      | .Withdrawal p => NEU_BoxModel.run (.Withdrawal (common a c) p) state
    else (ok (.Err solana_program_error.ProgramError.InvalidInstructionData),state,[])
  else (ok (.Err solana_program_error.ProgramError.InvalidAccountData),state,[])

def trace (request : Request) (a : Auth) (c : Candidate) :=
  if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
    if a.master.identity.asset_id=NDM_CohortReconstruction.requested request then
      match request.public with
      | .PrivateTransfer p => (NED_ValidatorTrace.run
          (NED_ReconstructCarriers.fromRaw (.PrivateTransfer (common a c) p))).2
      | .Withdrawal p => (NED_ValidatorTrace.run
          (NED_ReconstructCarriers.fromRaw (.Withdrawal (common a c) p))).2
    else []
  else []

/-- Model composition at the exact source calls. Constructor child hypotheses
are discharged by NEU_BoxModel; native auth/common/Box associations remain
separate certificate obligations, never premises hidden in this theorem. -/
theorem result_state_effects {State : Type} (request : Request) (a : Auth)
    (c : Candidate) (state : State) :
    run request a c state =
      (r1_pool_adapter.reconstruct_asq8_statement request a c,state,trace request a c) := by
  rw [NDM_CohortReconstruction.control]
  unfold run trace NDM_CohortReconstruction.direct
  by_cases gate : a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val
  · simp only [if_pos gate]
    by_cases asset : a.master.identity.asset_id=NDM_CohortReconstruction.requested request
    · simp only [if_pos asset]
      unfold NDM_CohortReconstruction.finish
      rw [common_result,bind_tc_ok]
      cases h : request.public with
      | PrivateTransfer p => exact NEU_BoxModel.transfer_result_state_effects (common a c) p state
      | Withdrawal p => exact NEU_BoxModel.withdrawal_result_state_effects (common a c) p state
    · simp only [if_neg asset]
  · simp only [if_neg gate]

#print axioms common_result
#print axioms result_state_effects
end NEU_ReconstructCore
