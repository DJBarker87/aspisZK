import Lean
import NFY_Part057
import NFY_Part053
import AspisR1TerminalDecoder.Funs
import RPz7_S6CurrentCodecInstallationV1
import NFY_Part034
import NFY_Part024
import NFY_Part041

-- BEGIN copied NEU_DecoderProjections: evidence/slice-s-compose7-20261103/NEU_DecoderProjections.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEU_DecoderProjections
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal
abbrev Common := PoolV1PairForestTerminalCommonV1
abbrev Transfer := NFY_NED_PaymentCohorts.T
abbrev Withdrawal := NFY_NED_PaymentCohorts.W

theorem common_ext (c d : Common)
    (point : ∀ slot i j k,
      NFY_NEU_CommonProjections.value (NFY_NED_ReconstructCarriers.toRawCommon c) slot i j k =
      NFY_NEU_CommonProjections.value (NFY_NED_ReconstructCarriers.toRawCommon d) slot i j k) : c=d := by
  have same := NFY_NEU_CommonProjections.common_ext _ _ point
  have back := congrArg NFY_NED_ReconstructCarriers.fromRawCommon same
  simpa only [NFY_NED_ReconstructCarriers.common_roundtrip] using back

theorem transfer_ext (c d : Common) (p q : Transfer)
    (commonPoint : ∀ slot i j k,
      NFY_NEU_CommonProjections.value (NFY_NED_ReconstructCarriers.toRawCommon c) slot i j k =
      NFY_NEU_CommonProjections.value (NFY_NED_ReconstructCarriers.toRawCommon d) slot i j k)
    (publicPoint : ∀ slot i j,
      NFY_NEU_PublicProjections.transfer (NFY_NED_PaymentCohorts.toRawTransfer p) slot i j =
      NFY_NEU_PublicProjections.transfer (NFY_NED_PaymentCohorts.toRawTransfer q) slot i j) :
    (PoolV1PairForestTerminalStatementV1.PrivateTransfer c p) = .PrivateTransfer d q := by
  have hc := common_ext c d commonPoint
  have hp := NFY_NEU_PublicProjections.transfer_ext _ _ publicPoint
  have raw : NFY_NED_ReconstructCarriers.toRaw (.PrivateTransfer c p) =
      NFY_NED_ReconstructCarriers.toRaw (.PrivateTransfer d q) := by
    change AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
      (NFY_NED_ReconstructCarriers.toRawCommon c) (NFY_NED_PaymentCohorts.toRawTransfer p) =
      .PrivateTransfer (NFY_NED_ReconstructCarriers.toRawCommon d) (NFY_NED_PaymentCohorts.toRawTransfer q)
    rw [hc,hp]
  have back := congrArg NFY_NED_ReconstructCarriers.fromRaw raw
  simpa only [NFY_NED_ReconstructCarriers.statement_roundtrip] using back

theorem withdrawal_ext (c d : Common) (p q : Withdrawal)
    (commonPoint : ∀ slot i j k,
      NFY_NEU_CommonProjections.value (NFY_NED_ReconstructCarriers.toRawCommon c) slot i j k =
      NFY_NEU_CommonProjections.value (NFY_NED_ReconstructCarriers.toRawCommon d) slot i j k)
    (publicPoint : ∀ slot i j,
      NFY_NEU_PublicProjections.withdrawal (NFY_NED_PaymentCohorts.toRawWithdrawal p) slot i j =
      NFY_NEU_PublicProjections.withdrawal (NFY_NED_PaymentCohorts.toRawWithdrawal q) slot i j) :
    (PoolV1PairForestTerminalStatementV1.Withdrawal c p) = .Withdrawal d q := by
  have hc := common_ext c d commonPoint
  have hp := NFY_NEU_PublicProjections.withdrawal_ext _ _ publicPoint
  have raw : NFY_NED_ReconstructCarriers.toRaw (.Withdrawal c p) =
      NFY_NED_ReconstructCarriers.toRaw (.Withdrawal d q) := by
    change AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
      (NFY_NED_ReconstructCarriers.toRawCommon c) (NFY_NED_PaymentCohorts.toRawWithdrawal p) =
      .Withdrawal (NFY_NED_ReconstructCarriers.toRawCommon d) (NFY_NED_PaymentCohorts.toRawWithdrawal q)
    rw [hc,hp]
  have back := congrArg NFY_NED_ReconstructCarriers.fromRaw raw
  simpa only [NFY_NED_ReconstructCarriers.statement_roundtrip] using back

theorem payment_packet (b : Array U8 216#usize) : b.to_slice.val.length=216 := b.property

#print axioms common_ext
#print axioms transfer_ext
#print axioms withdrawal_ext
#print axioms payment_packet
end NFY_NEU_DecoderProjections
-- END copied NEU_DecoderProjections
-- BEGIN copied NEX_TerminalOracle: evidence/slice-s-compose8-20261104/NEX_TerminalOracle.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEX_TerminalOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
def run (common : Slice U8 → Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (transfer : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 → Slice U8 → Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (withdrawal : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 → Slice U8 → Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (validate : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → Result (core.result.Result Unit pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (bytes : Slice Std.U8) : Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let i := Slice.len bytes
  let i1 ← pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
  if i != i1
  then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC { start := 0#usize, «end» := 4#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      if i2 != pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
      then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion)
      else
        let i3 ← Slice.index_usize bytes 5#usize
        let r ← pool_v1.pair_forest_terminal.transition_kind i3
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i4 ← Slice.index_usize bytes 6#usize
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding)
          else
            let r1 ← common bytes
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              match val with
              | pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer =>
                let i5 ← pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
                let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i5 }
                let r2 ← transfer val1 s2
                let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf2 with
                | core.ops.control_flow.ControlFlow.Continue val2 => let r3 ← validate val2
                                                                     let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
                                                                     match cf3 with
                                                                     | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok val2)
                                                                     | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
              | pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal =>
                let i5 ← pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
                let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i5 }
                let r2 ← withdrawal val1 s2
                let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf2 with
                | core.ops.control_flow.ControlFlow.Continue val2 => let r3 ← validate val2
                                                                     let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
                                                                     match cf3 with
                                                                     | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok val2)
                                                                     | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual

/-- Model continuation substitution only. Native certificates and reached
child domains are separate checked obligations; no native root is assumed. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1 pool_v1.pair_forest_terminal.decode_transfer_statement_boxed_v1 pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1 pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes,state,[]) := by rfl
#print axioms result_state_effects
end NFY_NEX_TerminalOracle
-- END copied NEX_TerminalOracle
-- BEGIN copied NEX_PublicModel: evidence/slice-s-compose8-20261104/NEX_PublicModel.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEX_PublicModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Statement := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev PE := AdapterRw.solana_program_error.ProgramError

def run (bytes : Slice U8) : Result (core.result.Result Statement PE) := do
  let reply ← NFY_NEX_TerminalOracle.run decode_terminal_common_boxed_v1
    decode_transfer_statement_boxed_v1 decode_withdrawal_statement_boxed_v1
    validate_pool_v1_pair_forest_terminal_statement_v1 bytes
  match reply with
  | .Ok value => ok (.Ok (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 value))
  | .Err _ => ok (.Err .InvalidAccountData)

/-- Endpoint is the coherent installed codec (op47), not a fresh decoder model.
The terminal child and carrier laws are reused. Native forwarding/Box evidence
must independently supply the ruling-(y)/(aa) part of the hybrid certificate. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run bytes,state,([] : List Unit)) =
    (AspisS6CurrentCodecInstallation.decode bytes,state,[]) := by
  have child := congrArg (fun x => x.1) (NFY_NEX_TerminalOracle.result_state_effects bytes state)
  dsimp only at child
  unfold run AspisS6CurrentCodecInstallation.decode
  rw [child,AspisS6CurrentCodecInstallation.boxed_eq]
  unfold AspisS6CurrentCodecInstallation.boxOps AspisS6CurrentCodecInstallation.rawDecoder
  dsimp only
  cases run : decode_pool_v1_pair_forest_terminal_statement_v1 bytes with
  | fail e => simp only [run,AspisS6OuterNativeOps.resultMap,bind_tc_fail]
  | div => simp only [run,AspisS6OuterNativeOps.resultMap,bind_tc_div]
  | ok reply => cases reply <;> simp only [run,AspisS6OuterNativeOps.resultMap,AspisS6CurrentCodecInstallation.mapBoth,bind_tc_ok]

#print axioms result_state_effects
#print axioms AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalStatementV1
end NFY_NEX_PublicModel
-- END copied NEX_PublicModel
-- BEGIN copied NEY_BindingContinuation: evidence/slice-s-compose9-20261104/NEY_BindingContinuation.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEY_BindingContinuation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
open AspisR1.S2K
abbrev Statement := StatementAdmission.Statement
abbrev Output := ResultAdmission.Output
abbrev Error := PoolV1PairForestTerminalFormatErrorV1

def run (sv : Statement → Result (core.result.Result Unit Error))
    (rv : Output → Result (core.result.Result Unit Error)) (s : Statement) :
    Result (core.result.Result Unit Error) := do
  let first ← sv s
  match first with
  | .Err e => ok (.Err e)
  | .Ok () => rv (ResultAdmission.value s)

/-- Total continuation on the caller-derived result. Neither validator success
is a premise; the complete first and second Results are preserved in order. -/
theorem result (s : Statement) :
    run validate_pool_v1_pair_forest_terminal_statement_v1 validate_result s =
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (ResultAdmission.value s) := by
  unfold run validate_pool_v1_pair_forest_terminal_result_against_statement_v1
  apply NFY_NBN_LateFactor.bind_ext
  intro first
  cases first with
  | Err e => rfl
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    cases step : validate_result (ResultAdmission.value s) with
    | fail e => simp only [step,bind_tc_fail]
    | div => simp only [step,bind_tc_div]
    | ok second =>
      simp only [step,bind_tc_ok]
      cases second with
      | Err e => rfl
      | Ok unit =>
       cases unit
       simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
       cases s <;> simp [ResultAdmission.value,ResultAdmission.kind,
        StatementAdmission.common,StatementChecks.nullifier,
        PoolV1PairForestTerminalStatementV1.common,
        PoolV1PairForestTerminalStatementV1.transition_kind,
        PoolV1PairForestTerminalStatementV1.nullifier,
        core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
        pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind.eq,
        ResultBinding.byte_array_ne_self,ResultBinding.digest_ne_self,ResultBinding.afterstate_self]

#print axioms result
end NFY_NEY_BindingContinuation
-- END copied NEY_BindingContinuation
-- BEGIN copied NEY_BindingSuccess: evidence/slice-s-compose9-20261104/NEY_BindingSuccess.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEY_BindingSuccess
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
open NFY_NEY_BindingContinuation

theorem first_success (s : Statement)
    (accepted : run validate_pool_v1_pair_forest_terminal_statement_v1 validate_result s = ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()) := by
  unfold run at accepted
  cases first : validate_pool_v1_pair_forest_terminal_statement_v1 s with
  | fail e => simp only [first,bind_tc_fail] at accepted; cases accepted
  | div => simp only [first,bind_tc_div] at accepted; cases accepted
  | ok outcome =>
    cases outcome with
    | Err e => simp only [first,bind_tc_ok] at accepted; cases accepted
    | Ok unit => cases unit; rfl

/-- Successful binding certifies its statement child on the SAME root input.
This supplies the encoder's reached accepted-statement domain, never a stronger
unproved precondition on emit_result. -/
theorem binding_success (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (AspisR1.S2K.ResultAdmission.value s) = ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()) := by
  apply first_success s
  rw [NFY_NEY_BindingContinuation.result]
  exact accepted

#print axioms first_success
#print axioms binding_success
end NFY_NEY_BindingSuccess
-- END copied NEY_BindingSuccess
-- BEGIN copied NEU_EmitModel: evidence/slice-s-compose7-20261103/NEU_EmitModel.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEU_EmitModel
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
abbrev Statement := AspisR1.S2K.StatementAdmission.Statement
abbrev Output := PoolV1PairForestTerminalResultV1
abbrev Error := PoolV1PairForestTerminalFormatErrorV1
abbrev ProgramError := AdapterRw.solana_program_error.ProgramError
abbrev Bytes := Array U8 792#usize
abbrev derived := AspisR1.S2K.ResultAdmission.value

/-- One model execution with explicit full child Results and return-data state.
No arbitrary reply is assumed successful. This is not an op53 instance. -/
def run {A E : Type}
    (binding : Statement → Output → Result (core.result.Result Unit Error))
    (encode : Output → Result (core.result.Result Bytes Error))
    (syscall : AspisR1.S2I.ReturnData.State A E → List U8 →
      Result (AspisR1.S2I.ReturnData.State A E))
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    Result (core.result.Result (AspisR1.S2I.ReturnData.State A E) ProgramError) := do
  let checked ← binding s (derived s)
  match checked with
  | .Err _ => ok (.Err .InvalidInstructionData)
  | .Ok () =>
    let encoded ← encode (derived s)
    match encoded with
    | .Err _ => ok (.Err .InvalidInstructionData)
    | .Ok bytes =>
      if bytes.val.length ≠ 792 then ok (.Err .InvalidInstructionData)
      else if bytes.val.take 4 ≠ [65#u8,83#u8,82#u8,56#u8] then ok (.Err .InvalidInstructionData)
      else do
        let state' ← syscall state bytes.val
        ok (.Ok state')

/-- The exact inner domains required at these two call sites, rather than a
uniform child bridge on unrelated records. They remain explicit hypotheses. -/
def BindingBridge (binding : Statement → Output → Result (core.result.Result Unit Error)) : Prop :=
  ∀ s, binding s (derived s) =
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s (derived s)
def EncoderBridge (encode : Output → Result (core.result.Result Bytes Error)) : Prop :=
  ∀ s, encode (derived s) = encode_pool_v1_pair_forest_terminal_result_v1 (derived s)

theorem result_state_effects {A E : Type}
    (binding : Statement → Output → Result (core.result.Result Unit Error))
    (encode : Output → Result (core.result.Result Bytes Error))
    (bindingBridge : BindingBridge binding) (encoderBridge : EncoderBridge encode)
    (syscall : AspisR1.S2I.ReturnData.State A E → List U8 →
      Result (AspisR1.S2I.ReturnData.State A E))
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    run binding encode syscall state s = AspisR1.NFY_JHb_Emit.source syscall state s := by
  unfold run AspisR1.NFY_JHb_Emit.source
  dsimp only
  rw [bindingBridge s, encoderBridge s]
  rfl

#print axioms result_state_effects
end NFY_NEU_EmitModel
-- END copied NEU_EmitModel
-- BEGIN copied NEU_EmitFrame: evidence/slice-s-compose7-20261103/NEU_EmitFrame.lean
set_option autoImplicit false
namespace NFY_NEU_EmitFrame
open AspisR1.S2I.ReturnData
open Aeneas Aeneas.Std
/-- A reached return-data syscall is observably not an empty event frame,
even if its returned Unit is erased. This keeps the op53 obstruction explicit. -/
theorem event_frame_changed {A E : Type} (state : State A E) (bytes : List U8) :
    (set state bytes).events ≠ state.events := by
  intro same
  change state.events ++ [.setReturnData bytes] = state.events at same
  have length := congrArg List.length same
  simp only [List.length_append, List.length_singleton] at length
  omega
#print axioms event_frame_changed
end NFY_NEU_EmitFrame
-- END copied NEU_EmitFrame
-- BEGIN copied NEX_ReturnData: evidence/slice-s-compose8-20261104/NEX_ReturnData.lean
set_option autoImplicit false
namespace NFY_NEX_ReturnData
open Aeneas Aeneas.Std Result
open AspisR1.S2I.ReturnData
/-- Ruling (ab), 2026-11-04, adds RuntimeReturnData as runtime trust. This
model law preserves the visible set-return-data event; it is not an op53
Unit-erasure or proof of Solana platform behaviour. -/
theorem set_preserves_order {A E : Type} (state : State A E) (bytes : Array U8 792#usize) :
    (set state bytes.val).events = state.events ++ [.setReturnData bytes.val] := by rfl

theorem runtime_bound (bytes : Array U8 792#usize) : bytes.val.length ≤ 1024 := by
  have length : bytes.val.length=792 := bytes.property
  omega

/-- Ruling (ab) is used by an emission certificate only if this event remains
in its ordered trace. The platform readback assumption is additional trust. -/
theorem observable {A E : Type} (state : State A E) (bytes : Array U8 792#usize) :
    (set state bytes.val).events ≠ state.events := NFY_NEU_EmitFrame.event_frame_changed state bytes.val

#print axioms set_preserves_order
#print axioms runtime_bound
#print axioms observable
end NFY_NEX_ReturnData
-- END copied NEX_ReturnData
-- BEGIN copied NEX_EmitRuntime: evidence/slice-s-compose8-20261104/NEX_EmitRuntime.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEX_EmitRuntime
open Aeneas Aeneas.Std Result
open NFY_NEU_EmitModel
/-- Ruling (ab): this trace-bearing runtime instance adds RuntimeReturnData.
BindingBridge and EncoderBridge remain explicit native obligations. -/
theorem result_state_effects {A E : Type}
    (binding : Statement → Output → Result (core.result.Result Unit NFY_NEU_EmitModel.Error))
    (encode : Output → Result (core.result.Result Bytes NFY_NEU_EmitModel.Error))
    (bindingBridge : BindingBridge binding) (encoderBridge : EncoderBridge encode)
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    run binding encode (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s =
    AspisR1.NFY_JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s :=
  NFY_NEU_EmitModel.result_state_effects binding encode bindingBridge encoderBridge _ state s

/-- Exact event position and no later write in the successful modeled path.
The native root association and native children are not supplied by this law. -/
theorem success {A E : Type}
    (binding : Statement → Output → Result (core.result.Result Unit NFY_NEU_EmitModel.Error))
    (encode : Output → Result (core.result.Result Bytes NFY_NEU_EmitModel.Error))
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) (bytes : Bytes)
    (hb : binding s (derived s) = ok (.Ok ()))
    (he : encode (derived s) = ok (.Ok bytes))
    (header : bytes.val.take 4 = [65#u8,83#u8,82#u8,56#u8]) :
    run binding encode (fun st raw => ok (AspisR1.S2I.ReturnData.set st raw)) state s =
    ok (.Ok (AspisR1.S2I.ReturnData.set state bytes.val)) := by
  unfold run
  rw [hb]
  simp only [bind_tc_ok]
  rw [he]
  simp only [bind_tc_ok]
  have hlen : bytes.val.length = 792 := bytes.property
  simp only [hlen, header, ne_eq, not_true_eq_false, ite_false, bind_tc_ok]

#print axioms result_state_effects
#print axioms success
end NFY_NEX_EmitRuntime
-- END copied NEX_EmitRuntime
-- BEGIN copied NEY_ResultEncoderOracle: evidence/slice-s-compose9-20261104/NEY_ResultEncoderOracle.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEY_ResultEncoderOracle
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1TerminalDecoder
abbrev Record := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
abbrev Error := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
abbrev After := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev AfterError := pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
def run
  (validate : Record → Result (core.result.Result Unit Error))
  (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize → Result (Array U8 32#usize))
  (after : After → Result (core.result.Result (Array U8 688#usize) AfterError))
  (result : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1) :
  Result (core.result.Result (Array Std.U8 792#usize)
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let r ← validate result
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let output := Array.repeat 792#usize 0#u8
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
        { «end» := 4#usize }
    let s1 ←
      lift (Array.to_slice
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output1 := index_mut_back s2
    let output2 ←
      Array.update output1 4#usize
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
    let i := read_discriminant result.transition_kind
    let i1 ← lift (UScalar.cast .U8 i)
    let output3 ← Array.update output2 5#usize i1
    let output4 ←
      Array.update output3 6#usize
        pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    let output5 ← Array.update output4 7#usize result.output_lane
    let (s3, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
        {
          start := pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET,
          «end» := pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET
        }
    let s4 ← lift (Array.to_slice result.master_account)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output6 := index_mut_back1 s5
    let (s6, index_mut_back2) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6
        {
          start := pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET,
          «end» := pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET
        }
    let s7 ← lift (Array.to_slice result.selected_lane_account)
    let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
    let output7 := index_mut_back2 s8
    let (s9, index_mut_back3) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output7
        {
          start := pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET,
          «end» := pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET
        }
    let a ← digest result.nullifier
    let s10 ← lift (Array.to_slice a)
    let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
    let output8 := index_mut_back3 s11
    let (s12, index_mut_back4) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output8
        { start := pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET }
    let r1 ←
      after result.verified_afterstate
    let r2 ←
      AspisR1TerminalDecoder.core.result.Result.map_err
        pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s13 ← lift (Array.to_slice val)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output9 := index_mut_back4 s14
      ok (core.result.Result.Ok output9)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 792#usize) (core.convert.FromSame
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 792#usize) (core.convert.FromSame
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
      residual

/-- Exact emitted-body substitution, including both error branches. Native
window/child-domain/frame certificates remain separate obligations. -/
theorem result_state_effects {State : Type} (record : Record) (state : State) :
    (run pool_v1.pair_forest_terminal.validate_result
      atomic_statement.encode_digest_canonical
      pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 record,
      state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1 record,
      state,[]) := by rfl
#print axioms result_state_effects
end NFY_NEY_ResultEncoderOracle
-- END copied NEY_ResultEncoderOracle
-- BEGIN copied NEY_EmitComposed: evidence/slice-s-compose9-20261104/NEY_EmitComposed.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEY_EmitComposed
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
open NFY_NEU_EmitModel

def encode (record : Output) : Result (core.result.Result Bytes NFY_NEU_EmitModel.Error) :=
  NFY_NEY_ResultEncoderOracle.run validate_result atomic_statement.encode_digest_canonical
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 record

theorem encoder_bridge : EncoderBridge encode := by
  intro s
  exact congrArg (fun value => value.1)
    (NFY_NEY_ResultEncoderOracle.result_state_effects (derived s) ())

/-- This reached path condition is derived from binding success on the SAME
statement. It is not a root precondition or a free callee-domain hypothesis. -/
theorem reached_encoder (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (derived s)=ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s=ok (.Ok ()) ∧
    encode (derived s)=ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) := by
  have valid := NFY_NEY_BindingSuccess.binding_success s accepted
  refine ⟨valid,?_⟩
  rw [encoder_bridge s]
  exact AspisR1.S2K.ResultPayload.encoded s valid

/-- Kernel MODEL part of the hybrid native certificate. Native source,
call domains and exact ordered return-data arguments require their independent
checked certificates. RuntimeReturnData is ADDED trust under ruling(ab). -/
theorem result_state_effects {A E : Type}
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    run validate_pool_v1_pair_forest_terminal_result_against_statement_v1 encode
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s =
    AspisR1.NFY_JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s :=
  NFY_NEX_EmitRuntime.result_state_effects _ encode (fun _ => rfl) encoder_bridge state s

#print axioms encoder_bridge
#print axioms reached_encoder
#print axioms result_state_effects
end NFY_NEY_EmitComposed
-- END copied NEY_EmitComposed
-- BEGIN copied NFD_CommonField00: evidence/slice-s-compose10-20261104/NFD_CommonField00.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField00
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get a.master_account j).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨0,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField00
-- END copied NFD_CommonField00
-- BEGIN copied NFD_CommonField01: evidence/slice-s-compose10-20261104/NFD_CommonField01.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField01
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get a.checkpoint_account j).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨1,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField01
-- END copied NFD_CommonField01
-- BEGIN copied NFD_CommonField02: evidence/slice-s-compose10-20261104/NFD_CommonField02.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField02
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get a.selected_lane_account j).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨2,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField02
-- END copied NFD_CommonField02
-- BEGIN copied NFD_CommonField03: evidence/slice-s-compose10-20261104/NFD_CommonField03.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField03
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  a.selected_lane.lane_id.val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨3,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField03
-- END copied NFD_CommonField03
-- BEGIN copied NFD_CommonField04: evidence/slice-s-compose10-20261104/NFD_CommonField04.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField04
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  a.checkpoint.checkpoint_sequence.val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨4,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField04
-- END copied NFD_CommonField04
-- BEGIN copied NFD_CommonField05: evidence/slice-s-compose10-20261104/NFD_CommonField05.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField05
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get a.checkpoint.global_root i).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨5,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField05
-- END copied NFD_CommonField05
-- BEGIN copied NFD_CommonField06: evidence/slice-s-compose10-20261104/NFD_CommonField06.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField06
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get a.live_snapshot.pool j).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨6,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField06
-- END copied NFD_CommonField06
-- BEGIN copied NFD_CommonField07: evidence/slice-s-compose10-20261104/NFD_CommonField07.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField07
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get a.live_snapshot.deployment_domain j).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨7,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField07
-- END copied NFD_CommonField07
-- BEGIN copied NFD_CommonField08: evidence/slice-s-compose10-20261104/NFD_CommonField08.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField08
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  a.live_snapshot.sequence.val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨8,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField08
-- END copied NFD_CommonField08
-- BEGIN copied NFD_CommonField09: evidence/slice-s-compose10-20261104/NFD_CommonField09.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField09
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  a.live_snapshot.next_pair_index.val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨9,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField09
-- END copied NFD_CommonField09
-- BEGIN copied NFD_CommonField10: evidence/slice-s-compose10-20261104/NFD_CommonField10.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField10
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get a.live_snapshot.current_root i).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨10,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField10
-- END copied NFD_CommonField10
-- BEGIN copied NFD_CommonField11: evidence/slice-s-compose10-20261104/NFD_CommonField11.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField11
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get (get a.live_snapshot.frontier k) i).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨11,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField11
-- END copied NFD_CommonField11
-- BEGIN copied NFD_CommonField12: evidence/slice-s-compose10-20261104/NFD_CommonField12.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField12
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  c.next_pair_index.val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨12,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField12
-- END copied NFD_CommonField12
-- BEGIN copied NFD_CommonField13: evidence/slice-s-compose10-20261104/NFD_CommonField13.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField13
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get c.next_root i).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨13,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField13
-- END copied NFD_CommonField13
-- BEGIN copied NFD_CommonField14: evidence/slice-s-compose10-20261104/NFD_CommonField14.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_CommonField14
open Aeneas Aeneas.Std NFY_NEU_ReconstructCore
open NFY_NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get (get c.next_frontier k) i).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NFY_NEU_CommonProjections.value (common a c) ⟨14,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFY_NFD_CommonField14
-- END copied NFD_CommonField14

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
