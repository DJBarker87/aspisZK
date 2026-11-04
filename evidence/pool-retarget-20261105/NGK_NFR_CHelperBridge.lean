import Lean
import NGK_NFR_CHelper

set_option autoImplicit false
noncomputable section
namespace NGK_NFR_CHelperBridge
open Aeneas Aeneas.Std Result
abbrev Output := NFY_NEU_EmitModel.Output
abbrev Bytes := Array U8 792#usize
abbrev EncodeError := NFY_NEU_EmitModel.Error
abbrev ProgramError := AdapterRw.solana_program_error.ProgramError

/-- Exact value-level semantics of the extracted frozen helper. Box allocation
is erased by Aeneas and therefore remains covered by the separate native cut. -/
def run (encoder : Output → Result (core.result.Result Bytes EncodeError)) (r : Output) :
    Result (core.result.Result Bytes ProgramError) := do
  let reply ← encoder r
  match reply with
  | .Ok bytes => ok (.Ok bytes)
  | .Err _ => ok (.Err NGK_NFR_CSettlement.invalidReturn)

theorem semantic (encoder : Output → Result (core.result.Result Bytes EncodeError)) (r : Output) :
    NGK_NFR_CHelper.terminal_ref encoder r = run encoder r := by
  cases reply : encoder r with
  | fail error =>
    simp only [NGK_NFR_CHelper.terminal_ref,NGK_NFR_CHelper.terminal_result_bytes_box_v1,run,reply,bind_tc_fail]
  | div =>
    simp only [NGK_NFR_CHelper.terminal_ref,NGK_NFR_CHelper.terminal_result_bytes_box_v1,run,reply,bind_tc_div]
  | ok answer =>
    cases answer with
    | Ok bytes =>
      rw [NGK_NFR_CHelper.accepted encoder r bytes reply]
      simp only [run,reply,bind_tc_ok]
    | Err error =>
      rw [NGK_NFR_CHelper.rejected encoder r error reply]
      simp only [run,reply,bind_tc_ok]

/-- The CLOSED encoder bridge is instantiated at the SAME emitted result.
Its statement domain follows from original statement validation. -/
theorem same_emission (s : NFY_NEU_EmitModel.Statement)
    (authenticated : NGK_NFO_ReadModel.Accepted)
    (same : authenticated.value = AspisR1.S2K.ResultAdmission.value s)
    (valid : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NGK_NFR_CHelper.terminal_ref NFY_NEY_EmitComposed.encode authenticated.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) :=
  NGK_NFR_CHelper.accepted _ _ _ (NGK_NFR_CSettlement.reencode_same s authenticated same valid)

#print axioms semantic
#print axioms same_emission
end NGK_NFR_CHelperBridge

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
