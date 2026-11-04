import Lean
import NFY_Part055
import NFY_Part054
import NFY_Part032
import NDM_Reference.Funs
import AdapterRwModel
import NFY_Part049
import NDM_GateRef.Funs

-- BEGIN copied NEE_RawValidatorPrefix: evidence/slice-s-compose2-20261029/NEE_RawValidatorPrefix.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_RawValidatorPrefix
open Aeneas Aeneas.Std Result AspisR1AdapterReconstruct NFY_NED_ErrorCarriers
abbrev RawStatement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev RawCommon := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev R := Result (core.result.Result Unit NFY_NED_RawValidatorControl.E)

def continuation (statement : RawStatement) (common : RawCommon) : R := do
  match statement with
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
    _ public1 =>
    let r ←
      aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
        public1
    let r1 ←
      AspisR1AdapterReconstruct.core.result.Result.map_err
        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (pool, deployment, anchor_sequence, anchor, nullifier, _) ←
        aspis_statement.pool_v1.pair_forest_terminal.statement_public_common
          statement
      let b3 ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 pool
          common.master_account
      if b3
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
      else
        let b4 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            deployment
            common.lane_transition.live_snapshot.deployment_domain
        if b4
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch)
        else
          let b5 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              common.lane_transition.live_snapshot.pool
              common.master_account
          if b5
          then
            ok (core.result.Result.Err
              aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
          else
            if anchor_sequence != common.checkpoint_sequence
            then
              ok (core.result.Result.Err
                aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch)
            else
              let b6 ←
                core.array.equality.PartialEqArray.ne
                  aspis_core.field.M31.Insts.CoreCmpPartialEqM31 anchor
                  common.historical_global_anchor
              if b6
              then
                ok (core.result.Result.Err
                  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch)
              else
                let r2 ←
                  aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
                    nullifier
                let r3 ←
                  AspisR1AdapterReconstruct.core.result.Result.map_err
                    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
                    r2 ()
                let cf1 ←
                  core.result.Result.Insts.CoreOpsTry.branch r3
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  if val != common.output_lane
                  then
                    ok (core.result.Result.Err
                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
                  else
                    let late_bytes := Array.repeat 1520#usize 0#u8
                    let (s, _) ← lift (Array.to_slice_mut late_bytes)
                    let (r4, _) ←
                      aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
                        common.lane_transition s
                    let r5 ←
                      AspisR1AdapterReconstruct.core.result.Result.map_err
                        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
                        r4 ()
                    let cf2 ←
                      core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf2 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      ok (core.result.Result.Ok ())
                    | core.ops.control_flow.ControlFlow.Break residual
                      =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
    _ public1 =>
    let r ←
      aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
        public1
    let r1 ←
      AspisR1AdapterReconstruct.core.result.Result.map_err
        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (pool, deployment, anchor_sequence, anchor, nullifier, _) ←
        aspis_statement.pool_v1.pair_forest_terminal.statement_public_common
          statement
      let b3 ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 pool
          common.master_account
      if b3
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
      else
        let b4 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            deployment
            common.lane_transition.live_snapshot.deployment_domain
        if b4
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch)
        else
          let b5 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              common.lane_transition.live_snapshot.pool
              common.master_account
          if b5
          then
            ok (core.result.Result.Err
              aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
          else
            if anchor_sequence != common.checkpoint_sequence
            then
              ok (core.result.Result.Err
                aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch)
            else
              let b6 ←
                core.array.equality.PartialEqArray.ne
                  aspis_core.field.M31.Insts.CoreCmpPartialEqM31 anchor
                  common.historical_global_anchor
              if b6
              then
                ok (core.result.Result.Err
                  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch)
              else
                let r2 ←
                  aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
                    nullifier
                let r3 ←
                  AspisR1AdapterReconstruct.core.result.Result.map_err
                    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
                    r2 ()
                let cf1 ←
                  core.result.Result.Insts.CoreOpsTry.branch r3
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  if val != common.output_lane
                  then
                    ok (core.result.Result.Err
                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
                  else
                    let late_bytes := Array.repeat 1520#usize 0#u8
                    let (s, _) ← lift (Array.to_slice_mut late_bytes)
                    let (r4, _) ←
                      aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
                        common.lane_transition s
                    let r5 ←
                      AspisR1AdapterReconstruct.core.result.Result.map_err
                        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
                        r4 ()
                    let cf2 ←
                      core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf2 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      ok (core.result.Result.Ok ())
                    | core.ops.control_flow.ControlFlow.Break residual
                      =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual


def gate (common : RawCommon) (next : R) : R := do
  let a := Array.repeat 32#usize 0#u8
  let b ←
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      common.master_account a
  if b
  then
    ok (core.result.Result.Err
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ←
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        common.checkpoint_account a1
    if b1
    then
      ok (core.result.Result.Err
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
    else
      let a2 := Array.repeat 32#usize 0#u8
      let b2 ←
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
          common.selected_lane_account a2
      if b2
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
      else
        let i ← lift (core.convert.num.FromUsizeU8.from common.output_lane)
        if i >=
          aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidOutputLane)
        else
          next

theorem source_factor (s : RawStatement) :
    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s =
    (do let c ← aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common s
        gate c (continuation s c)) := by rfl

#print axioms source_factor
end NFY_NEE_RawValidatorPrefix
-- END copied NEE_RawValidatorPrefix
-- BEGIN copied NEE_ValidatorGate: evidence/slice-s-compose2-20261029/NEE_ValidatorGate.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ValidatorGate
open Aeneas Aeneas.Std Result AspisR1AdapterReconstruct
open NFY_NBN_StatementResult NFY_NED_ErrorCarriers
attribute [local instance] Classical.propDecidable

def normalized (c : NFY_NED_ReconstructCarriers.Common) (next : NFY_NEE_RawValidatorPrefix.R) : NFY_NEE_RawValidatorPrefix.R :=
  if c.master_account = zero ∨ c.checkpoint_account = zero ∨ c.selected_lane_account = zero
  then ok (.Err .NonZeroBinding)
  else if 8 ≤ c.output_lane.val then ok (.Err .InvalidOutputLane) else next

/-- Prefix transport is independent of every child computation. -/
theorem result (c : NFY_NED_ReconstructCarriers.Common) (next : NFY_NEE_RawValidatorPrefix.R) :
    NFY_NEE_RawValidatorPrefix.gate (NFY_NED_ReconstructCarriers.toRawCommon c) next =
    normalized c next := by
  unfold NFY_NEE_RawValidatorPrefix.gate normalized
  simp only [NBH_ArrayEq.source,bind_tc_ok,NFY_NED_StatementCarrierFields.master,
    NFY_NED_StatementCarrierFields.checkpoint,NFY_NED_StatementCarrierFields.selected_lane,
    NFY_NED_StatementCarrierFields.lane,decide_eq_true_eq]
  have cast : core.convert.num.FromUsizeU8.from c.output_lane =
      Usize.ofNatCore c.output_lane.val (by scalar_tac) := by scalar_tac
  simp only [cast,lift,bind_tc_ok,
    aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT]
  by_cases hm : c.master_account = zero
  · simp only [zero] at hm
    simp only [hm,decide_true,if_true,true_or]
  · by_cases hc : c.checkpoint_account = zero
    · simp only [zero] at hm hc
      simp only [hm,hc,decide_false,decide_true,if_false,if_true,false_or,true_or]
    · by_cases hs : c.selected_lane_account = zero
      · simp only [zero] at hm hc hs
        simp only [hm,hc,hs,decide_false,decide_true,if_false,if_true,false_or]
      · by_cases lane : 8 ≤ c.output_lane.val
        · have large : (Usize.ofNatCore c.output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
          simp only [zero] at hm hc hs
          simp only [hm,hc,hs,decide_false,if_false,false_or,lane,large,if_true]
        · have small : ¬ (Usize.ofNatCore c.output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
          simp only [zero] at hm hc hs
          simp only [hm,hc,hs,decide_false,if_false,false_or,lane,small]

#print axioms result
end NFY_NEE_ValidatorGate
-- END copied NEE_ValidatorGate
-- BEGIN copied NEE_ValidatorContinuation: evidence/slice-s-compose2-20261029/NEE_ValidatorContinuation.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ValidatorContinuation
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult AspisR1AdapterReconstruct
open NFY_NED_ErrorCarriers
abbrev RawPayment := Result (core.result.Result (Array U8 216#usize)
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)

def payment (s : Statement) : RawPayment :=
  match s with
  | .PrivateTransfer _ p => aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
      (NFY_NED_PaymentCohorts.toRawTransfer p)
  | .Withdrawal _ p => aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
      (NFY_NED_PaymentCohorts.toRawWithdrawal p)

def run (s : Statement) : NFY_NEE_RawValidatorPrefix.R := do
  let r ← payment s
  match r with
  | .Err e => ok (.Err (.Payment e))
  | .Ok _ => NFY_NED_RawValidatorBindings.run s

/-- The complete raw continuation, with payment still left as an arbitrary
child Result. No source child is unfolded and no successful-parent premise is used. -/
theorem source_factor (s : Statement) :
    NFY_NEE_RawValidatorPrefix.continuation (NFY_NED_ReconstructCarriers.toRaw s)
      (NFY_NED_ReconstructCarriers.toRawCommon (common s)) = run s := by
  cases s with
  | PrivateTransfer c p =>
    unfold NFY_NEE_RawValidatorPrefix.continuation run payment
    rw [NFY_NED_StatementCarrierFields.transfer]
    apply NFY_NBN_LateFactor.bind_ext
    intro r
    cases r <;> rfl
  | Withdrawal c p =>
    unfold NFY_NEE_RawValidatorPrefix.continuation run payment
    rw [NFY_NED_StatementCarrierFields.withdrawal]
    apply NFY_NBN_LateFactor.bind_ext
    intro r
    cases r <;> rfl

#print axioms source_factor
end NFY_NEE_ValidatorContinuation
-- END copied NEE_ValidatorContinuation
-- BEGIN copied NEE_ValidatorContinuationResult: evidence/slice-s-compose2-20261029/NEE_ValidatorContinuationResult.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ValidatorContinuationResult
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult NFY_NED_ErrorCarriers

def model (s : Statement) : core.result.Result Unit NFY_NBN_StatementResult.Error :=
  match NFY_NED_ValidatorStatus.payment s with
  | .Err e => .Err (.Payment e)
  | .Ok _ => suffix s

theorem payment (s : Statement) : NFY_NEE_ValidatorContinuation.payment s =
    ok (NFY_NED_CommonValidation.mapPayment (NFY_NED_ValidatorStatus.payment s)) := by
  cases s with
  | PrivateTransfer c p => exact NFY_NED_TransferEncodingCohort.result p
  | Withdrawal c p => exact NFY_NED_WithdrawalEncodingCohort.result p

theorem result (s : Statement) : NFY_NEE_ValidatorContinuation.run s =
    ok (NFY_NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1 (model s)) := by
  unfold NFY_NEE_ValidatorContinuation.run model
  rw [payment]
  cases h : NFY_NED_ValidatorStatus.payment s with
  | Err e => rfl
  | Ok bytes =>
    simp only [NFY_NED_CommonValidation.mapPayment,bind_tc_ok]
    exact NFY_NEE_ValidatorBindings.result s

#print axioms payment
#print axioms result
end NFY_NEE_ValidatorContinuationResult
-- END copied NEE_ValidatorContinuationResult
-- BEGIN copied NEE_RawValidatorCohort: evidence/slice-s-compose2-20261029/NEE_RawValidatorCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_RawValidatorCohort
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult NFY_NED_ErrorCarriers
open AspisR1AdapterReconstruct
attribute [local instance] Classical.propDecidable

/-- Total emitted-family transport, including every rejection/error. This is
the model substitution part of the native composition, not a native-root claim. -/
theorem result (s : Statement) :
    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      (NFY_NED_ReconstructCarriers.toRaw s) =
    ok (NFY_NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1
      (NFY_NED_ValidatorStatus.status s)) := by
  rw [NFY_NEE_RawValidatorPrefix.source_factor,NFY_NED_ReconstructCarriers.common_argument]
  simp only [bind_tc_ok]
  rw [NFY_NEE_ValidatorGate.result,NFY_NEE_ValidatorContinuation.source_factor,
    NFY_NEE_ValidatorContinuationResult.result]
  unfold NFY_NEE_ValidatorGate.normalized NFY_NED_ValidatorStatus.status NFY_NEE_ValidatorContinuationResult.model
  dsimp (config := {zeta := true,zetaHave := true}) only
  by_cases hz : (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero
  · simp only [hz,if_true]
    rfl
  · simp only [hz,if_false]
    by_cases hl : 8 ≤ (common s).output_lane.val
    · simp only [hl,if_true]
      rfl
    · simp only [hl,if_false]
      rfl

#print axioms result
end NFY_NEE_RawValidatorCohort
-- END copied NEE_RawValidatorCohort
-- BEGIN copied NEU_BoxModel: evidence/slice-s-compose7-20261103/NEU_BoxModel.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEU_BoxModel
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Transfer := payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := payment_relation.PoolV1WithdrawalPublicV1
abbrev Error := pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
abbrev ProgramError := AspisR1AdapterReconstruct.solana_program_error.ProgramError

def status (s : Statement) : core.result.Result Unit Error :=
  NFY_NED_LateValidatorCohorts.mapResult NFY_NED_ErrorCarriers.toRawPoolV1PairForestTerminalFormatErrorV1
    (NFY_NED_ValidatorStatus.status (NFY_NED_ReconstructCarriers.fromRaw s))

def wrap (s : Statement) (r : core.result.Result Unit Error) :
    core.result.Result Statement ProgramError :=
  match r with | .Ok _ => .Ok s | .Err _ => .Err .InvalidInstructionData

theorem validator (s : Statement) :
    pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (status s) := by
  have h := NFY_NEE_RawValidatorCohort.result (NFY_NED_ReconstructCarriers.fromRaw s)
  rw [NFY_NED_RawCarrierInverses.statement] at h
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
  let observed := NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay NFY_NEM_LaneReached.lane
    NFY_NEM_LateOracle.late (NFY_NED_ReconstructCarriers.fromRaw s)
  ((do let reply ← observed.1
       ok (wrap s (NFY_NED_LateValidatorCohorts.mapResult
         NFY_NED_ErrorCarriers.toRawPoolV1PairForestTerminalFormatErrorV1 reply))),state,observed.2)

theorem transfer_result_state_effects {State : Type} (c : Common) (p : Transfer) (state : State) :
    run (.PrivateTransfer c p) state =
    (r1_pool_adapter.transfer_statement_box c p,state,
      (NFY_NED_ValidatorTrace.run (NFY_NED_ReconstructCarriers.fromRaw (.PrivateTransfer c p))).2) := by
  have child := NFY_NEM_ValidatorComposed.result_state_effects
    (NFY_NED_ReconstructCarriers.fromRaw (.PrivateTransfer c p)) state
  have reply := congrArg (fun x => x.1) child
  have trace := congrArg (fun x => x.2.2) child
  dsimp only at reply trace
  unfold run
  dsimp only
  rw [reply,trace,NFY_NED_ValidatorStatus.source,bind_tc_ok,transfer]
  rfl

theorem withdrawal_result_state_effects {State : Type} (c : Common) (p : Withdrawal) (state : State) :
    run (.Withdrawal c p) state =
    (r1_pool_adapter.withdrawal_statement_box c p,state,
      (NFY_NED_ValidatorTrace.run (NFY_NED_ReconstructCarriers.fromRaw (.Withdrawal c p))).2) := by
  have child := NFY_NEM_ValidatorComposed.result_state_effects
    (NFY_NED_ReconstructCarriers.fromRaw (.Withdrawal c p)) state
  have reply := congrArg (fun x => x.1) child
  have trace := congrArg (fun x => x.2.2) child
  dsimp only at reply trace
  unfold run
  dsimp only
  rw [reply,trace,NFY_NED_ValidatorStatus.source,bind_tc_ok,withdrawal]
  rfl

#print axioms validator
#print axioms transfer
#print axioms withdrawal
#print axioms transfer_result_state_effects
#print axioms withdrawal_result_state_effects
end NFY_NEU_BoxModel
-- END copied NEU_BoxModel
-- BEGIN copied NDM_CommonCarrier: evidence/native-front4b-20261028/NDM_CommonCarrier.lean
set_option autoImplicit false
namespace NFY_NDM_CommonCarrier
open Aeneas Aeneas.Std Result
open AdapterRw
open aspis_statement.pool_v1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Candidate := pair_terminal.PoolV1PairVerifiedAfterstateV1

def value (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : Candidate) : Common :=
 ⟨a.master_account,a.checkpoint_account,a.selected_lane_account,a.selected_lane.lane_id,
  a.checkpoint.checkpoint_sequence,a.checkpoint.global_root,⟨a.live_snapshot,c⟩⟩

def project (c : Common) := (c.master_account,c.checkpoint_account,c.selected_lane_account,
 c.output_lane,c.checkpoint_sequence,c.historical_global_anchor,
 c.lane_transition.live_snapshot,c.lane_transition.candidate_afterstate)

theorem reference (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : Candidate) :
 NDM_Reference.common_ref a.master_account a.checkpoint_account a.selected_lane_account
 a.selected_lane.lane_id a.checkpoint.checkpoint_sequence a.checkpoint.global_root
 a.live_snapshot c = ok (project (value a c)) := rfl

theorem project_injective (a b : Common) (same : project a = project b) : a=b := by
 cases a with
 | mk am ac al ao asq ah atr =>
  cases b with
  | mk bm bc bl bo bsq bh btr =>
   cases atr
   cases btr
   simp_all [project]

/-- This is a carrier equality. The native projection hypotheses are separate obligations. -/
theorem assemble (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : Candidate)
 (actual : Common) (windows : project actual = project (value a c)) :
 actual = value a c := project_injective actual (value a c) windows

#print axioms reference
#print axioms project_injective
#print axioms assemble
end NFY_NDM_CommonCarrier
-- END copied NDM_CommonCarrier
-- BEGIN copied NDM_CohortCommon: evidence/native-front4b-20261028/NDM_CohortCommon.lean
set_option autoImplicit false
namespace NFY_NDM_CohortCommon
open Aeneas Aeneas.Std Result
open AspisR1.JHf_Carrier

theorem emitted (a : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
 (c : NFY_NDM_CommonCarrier.Candidate) :
 AspisR1AdapterReconstruct.r1_pool_adapter.asq8_common
  (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)=
 ok (toPoolV1PairForestTerminalCommonV1 (NFY_NDM_CommonCarrier.value a c)) := rfl

/-- Association is to the actual emitted common constructor consumed by op52,
 not a standalone free cohort slot. Native Box transport remains OPEN. -/
theorem cohort (a : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
 (c : NFY_NDM_CommonCarrier.Candidate) :
 (do let raw ← AspisR1AdapterReconstruct.r1_pool_adapter.asq8_common
       (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)
     ok (NFY_NDM_CommonCarrier.project (fromPoolV1PairForestTerminalCommonV1 raw)))=
 NDM_Reference.common_ref a.master_account a.checkpoint_account a.selected_lane_account
 a.selected_lane.lane_id a.checkpoint.checkpoint_sequence a.checkpoint.global_root
 a.live_snapshot c := by
 rw [emitted]
 rfl

#print axioms emitted
#print axioms cohort
end NFY_NDM_CohortCommon
-- END copied NDM_CohortCommon
-- BEGIN copied NDM_NextGate: evidence/native-front4b-20261028/NDM_NextGate.lean
set_option autoImplicit false
namespace NFY_NDM_NextGate
open Aeneas Aeneas.Std Result

theorem exact_next (live next : U64) (step : next.val=live.val+1) :
 NDM_GateRef.next_gate_ref live next=ok true := by
 obtain ⟨out,run,meaning⟩ := WP.spec_imp_exists
  (UScalar.add_spec (x:=live) (y:=1#u64) (by scalar_tac))
 have same : out=next := by scalar_tac
 have call : U64.checked_add live 1#u64=some next := by
  change Option.ofResult (live+1#u64)=some next
  rw [run,same]
  rfl
 simp [NDM_GateRef.next_gate_ref,call,lift]

#print axioms exact_next
#print Aeneas.Std.UScalar.tryMk
end NFY_NDM_NextGate
-- END copied NDM_NextGate
-- BEGIN copied NDM_GateTotal: evidence/native-front4b-20261028/NDM_GateTotal.lean
set_option autoImplicit false
namespace NFY_NDM_GateTotal
open Aeneas Aeneas.Std Result

theorem reference (live next : U64) :
 NDM_GateRef.next_gate_ref live next = ok (decide (live.val+1=next.val)) := by
 by_cases bounded : live.val+1 ≤ U64.max
 · obtain ⟨out,run,meaning⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=live) (y:=1#u64) (by simpa using bounded))
   have call : U64.checked_add live 1#u64=some out := by
    change Option.ofResult (live+1#u64)=some out
    rw [run]
    rfl
   have value : out.val=live.val+1 := by simpa using meaning
   have eqv : out=next ↔ live.val+1=next.val := by
    constructor
    · intro h; simpa only [h] using value.symm
    · intro h; exact UScalar.eq_of_val_eq (value.trans h)
   simp [NDM_GateRef.next_gate_ref,call,lift,eqv]
 · have neq : live.val+1≠next.val := by scalar_tac
   have large : ¬ live.val+1 < 18446744073709551616 := by scalar_tac
   have call : U64.checked_add live 1#u64=none := by
    change Option.ofResult (UScalar.tryMk .U64 (live.val+1))=none
    simp [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds, large,
      Option.ofResult,ofOption]
   simp [NDM_GateRef.next_gate_ref,call,lift,neq]

#print axioms reference
end NFY_NDM_GateTotal
-- END copied NDM_GateTotal

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
