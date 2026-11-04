import Lean
import NGK_NFR_CSettlement

set_option autoImplicit false
noncomputable section
namespace NGK_NFR_CHelper
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
@[discriminant u32 [1095966721,1095966722,1095966723,1095966724,1095966725,1095966726,1095966727,1095966728,1095966729,1095966730,1095966731,1095966732,1095966733,1095966734,1095966735,1095966736,1095966737,1095966738,1095966739,1095966740,1095966741,1095966742,1095966743,1095966744,1095966745,1095966746,1095966747,1095966748,1095966749,1095966750,1095966751,1095966752,1095966753,1095966754,1095966755,1095966756,1095966757,1095966758,1095966759,1095966760,1095966761,1095966762,1095966763,1095966764,1095966765,1095966766,1095966767,1095966768,1095966769,1095966770,1095966771,1095966772,1095966773,1095966774]]
inductive aspis_pool.error.PoolV1ProgramError where
| InvalidAccountType : aspis_pool.error.PoolV1ProgramError
| InvalidRootPageAddress : aspis_pool.error.PoolV1ProgramError
| StateHistoryMismatch : aspis_pool.error.PoolV1ProgramError
| TreeFull : aspis_pool.error.PoolV1ProgramError
| InsufficientTreeCapacity : aspis_pool.error.PoolV1ProgramError
| UnexpectedRootPage : aspis_pool.error.PoolV1ProgramError
| NonCanonicalLeaf : aspis_pool.error.PoolV1ProgramError
| ArithmeticOverflow : aspis_pool.error.PoolV1ProgramError
| InvalidPoolStateAddress : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierRegistryAddress : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierEntryAddress : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierRegistry : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierEntry : aspis_pool.error.PoolV1ProgramError
| VerifierRegistryPaused : aspis_pool.error.PoolV1ProgramError
| VerifierEntryInactive : aspis_pool.error.PoolV1ProgramError
| VerifierEntryNotActiveYet : aspis_pool.error.PoolV1ProgramError
| VerifierEntryRetired : aspis_pool.error.PoolV1ProgramError
| VerifierSelectionMismatch : aspis_pool.error.PoolV1ProgramError
| InvalidTokenProgram : aspis_pool.error.PoolV1ProgramError
| InvalidMint : aspis_pool.error.PoolV1ProgramError
| InvalidTokenAccount : aspis_pool.error.PoolV1ProgramError
| InvalidVaultAuthority : aspis_pool.error.PoolV1ProgramError
| InvalidVaultTokenAddress : aspis_pool.error.PoolV1ProgramError
| InvalidDepositAmount : aspis_pool.error.PoolV1ProgramError
| InsufficientDepositFunds : aspis_pool.error.PoolV1ProgramError
| UnsupportedTokenConfiguration : aspis_pool.error.PoolV1ProgramError
| InvalidEncryptedNotePayload : aspis_pool.error.PoolV1ProgramError
| TokenBalanceDeltaMismatch : aspis_pool.error.PoolV1ProgramError
| InvalidSourceAuthority : aspis_pool.error.PoolV1ProgramError
| InvalidHistoricalAnchorEnvelope : aspis_pool.error.PoolV1ProgramError
| HistoricalAnchorIdentityMismatch : aspis_pool.error.PoolV1ProgramError
| HistoricalAnchorSelectionMismatch : aspis_pool.error.PoolV1ProgramError
| HistoricalAnchorInFuture : aspis_pool.error.PoolV1ProgramError
| InvalidHistoricalAnchorPage : aspis_pool.error.PoolV1ProgramError
| HistoricalAnchorRootMismatch : aspis_pool.error.PoolV1ProgramError
| InvalidNullifierMarkerAddress : aspis_pool.error.PoolV1ProgramError
| InvalidNullifierMarkerAccount : aspis_pool.error.PoolV1ProgramError
| NullifierAlreadyConsumed : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierProgramAccount : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierProofAccount : aspis_pool.error.PoolV1ProgramError
| VerifierProofBindingMismatch : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierDispatchEnvelope : aspis_pool.error.PoolV1ProgramError
| VerifierDispatchIdentityMismatch : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierReturnProgram : aspis_pool.error.PoolV1ProgramError
| InvalidVerifierReturnData : aspis_pool.error.PoolV1ProgramError
| VerifierResultBindingMismatch : aspis_pool.error.PoolV1ProgramError
| MissingVerifierReturnData : aspis_pool.error.PoolV1ProgramError
| InvalidWithdrawalAmount : aspis_pool.error.PoolV1ProgramError
| InsufficientVaultFunds : aspis_pool.error.PoolV1ProgramError
| InvalidDestinationTokenAccount : aspis_pool.error.PoolV1ProgramError
| InvalidSystemProgram : aspis_pool.error.PoolV1ProgramError
| InvalidPayer : aspis_pool.error.PoolV1ProgramError
| InvalidFreshAccount : aspis_pool.error.PoolV1ProgramError
| CpiInvocationForbidden : aspis_pool.error.PoolV1ProgramError


def terminal_result_bytes_box_v1.closure := Unit


def
  convertPoolError
  (error : aspis_pool.error.PoolV1ProgramError) :
  Result AdapterRw.solana_program_error.ProgramError
  := do
  let error1 := read_discriminant error
  let i ← lift (UScalar.cast .U32 error1)
  ok (AdapterRw.solana_program_error.ProgramError.Custom i)



def poolErrorFrom :
  core.convert.From AdapterRw.solana_program_error.ProgramError
  aspis_pool.error.PoolV1ProgramError := {
  «from» :=
    convertPoolError
}


def
  terminal_result_bytes_box_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1PoolV1ProgramError.call_once
  (c : terminal_result_bytes_box_v1.closure)
  (tupled_args :
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result aspis_pool.error.PoolV1ProgramError
  := do
  ok aspis_pool.error.PoolV1ProgramError.InvalidVerifierReturnData



def
  terminal_result_bytes_box_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1PoolV1ProgramError
  : core.ops.function.FnOnce terminal_result_bytes_box_v1.closure
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  aspis_pool.error.PoolV1ProgramError := {
  call_once :=
    terminal_result_bytes_box_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1PoolV1ProgramError.call_once
}


def terminal_result_bytes_box_v1
  (encoder : NFY_NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NFY_NEU_EmitModel.Error))
  (result :
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1)
  :
  Result (core.result.Result (Array Std.U8 792#usize)
    AdapterRw.solana_program_error.ProgramError)
  := do
  let r ←
    encoder result
  let r1 ←
    core.result.Result.map_err
      terminal_result_bytes_box_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1PoolV1ProgramError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 792#usize)
      poolErrorFrom
      residual


def terminal_ref
  (encoder : NFY_NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NFY_NEU_EmitModel.Error))
  (result :
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1)
  :
  Result (core.result.Result (Array Std.U8 792#usize)
    AdapterRw.solana_program_error.ProgramError)
  := do
  terminal_result_bytes_box_v1 encoder result



theorem accepted (encoder : NFY_NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NFY_NEU_EmitModel.Error))
    (r : NFY_NEU_EmitModel.Output) (bytes : Array U8 792#usize)
    (encoded : encoder r = ok (.Ok bytes)) :
    terminal_ref encoder r = ok (.Ok bytes) := by
  unfold terminal_ref terminal_result_bytes_box_v1
  rw [encoded]
  rfl

theorem rejected (encoder : NFY_NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NFY_NEU_EmitModel.Error))
    (r : NFY_NEU_EmitModel.Output) (e : NFY_NEU_EmitModel.Error)
    (encoded : encoder r = ok (.Err e)) :
    terminal_ref encoder r = ok (.Err NGK_NFR_CSettlement.invalidReturn) := by
  unfold terminal_ref terminal_result_bytes_box_v1
  rw [encoded]
  rfl

#print axioms accepted
#print axioms rejected
end NGK_NFR_CHelper

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
