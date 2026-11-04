import NEE_RawValidatorCohort
import NED_RawCarrierInverses
import NEM_ValidatorComposed
set_option autoImplicit false
noncomputable section
namespace NEU_BoxModel
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Transfer := payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := payment_relation.PoolV1WithdrawalPublicV1
abbrev Error := pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
abbrev ProgramError := AspisR1AdapterReconstruct.solana_program_error.ProgramError

def status (s : Statement) : core.result.Result Unit Error :=
  NED_LateValidatorCohorts.mapResult NED_ErrorCarriers.toRawPoolV1PairForestTerminalFormatErrorV1
    (NED_ValidatorStatus.status (NED_ReconstructCarriers.fromRaw s))

def wrap (s : Statement) (r : core.result.Result Unit Error) :
    core.result.Result Statement ProgramError :=
  match r with | .Ok _ => .Ok s | .Err _ => .Err .InvalidInstructionData

theorem validator (s : Statement) :
    pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (status s) := by
  have h := NEE_RawValidatorCohort.result (NED_ReconstructCarriers.fromRaw s)
  rw [NED_RawCarrierInverses.statement] at h
  exact h

/-- Complete arbitrary-input emitted constructor Result, including every
validation rejection. The old sameCall premise is discharged, not packaged. -/
theorem transfer (c : Common) (p : Transfer) :
    r1_pool_adapter.transfer_statement_box c p =
      ok (wrap (.PrivateTransfer c p) (status (.PrivateTransfer c p))) := by
  unfold r1_pool_adapter.transfer_statement_box
  rw [validator]
  cases status (.PrivateTransfer c p) <;> rfl

theorem withdrawal (c : Common) (p : Withdrawal) :
    r1_pool_adapter.withdrawal_statement_box c p =
      ok (wrap (.Withdrawal c p) (status (.Withdrawal c p))) := by
  unfold r1_pool_adapter.withdrawal_statement_box
  rw [validator]
  cases status (.Withdrawal c p) <;> rfl

/-- Child execution is the already composed validator oracle, at precisely
this constructed raw statement's canonical carrier. -/
def run {State : Type} (s : Statement) (state : State) :=
  let observed := NEE_ValidatorOracle.run NEM_PaymentReached.pay NEM_LaneReached.lane
    NEM_LateOracle.late (NED_ReconstructCarriers.fromRaw s)
  ((do let reply ← observed.1
       ok (wrap s (NED_LateValidatorCohorts.mapResult
         NED_ErrorCarriers.toRawPoolV1PairForestTerminalFormatErrorV1 reply))),state,observed.2)

theorem transfer_result_state_effects {State : Type} (c : Common) (p : Transfer) (state : State) :
    run (.PrivateTransfer c p) state =
    (r1_pool_adapter.transfer_statement_box c p,state,
      (NED_ValidatorTrace.run (NED_ReconstructCarriers.fromRaw (.PrivateTransfer c p))).2) := by
  have child := NEM_ValidatorComposed.result_state_effects
    (NED_ReconstructCarriers.fromRaw (.PrivateTransfer c p)) state
  have reply := congrArg (fun x => x.1) child
  have trace := congrArg (fun x => x.2.2) child
  dsimp only at reply trace
  unfold run
  dsimp only
  rw [reply,trace,NED_ValidatorStatus.source,bind_tc_ok,transfer]
  rfl

theorem withdrawal_result_state_effects {State : Type} (c : Common) (p : Withdrawal) (state : State) :
    run (.Withdrawal c p) state =
    (r1_pool_adapter.withdrawal_statement_box c p,state,
      (NED_ValidatorTrace.run (NED_ReconstructCarriers.fromRaw (.Withdrawal c p))).2) := by
  have child := NEM_ValidatorComposed.result_state_effects
    (NED_ReconstructCarriers.fromRaw (.Withdrawal c p)) state
  have reply := congrArg (fun x => x.1) child
  have trace := congrArg (fun x => x.2.2) child
  dsimp only at reply trace
  unfold run
  dsimp only
  rw [reply,trace,NED_ValidatorStatus.source,bind_tc_ok,withdrawal]
  rfl

#print axioms validator
#print axioms transfer
#print axioms withdrawal
#print axioms transfer_result_state_effects
#print axioms withdrawal_result_state_effects
end NEU_BoxModel
