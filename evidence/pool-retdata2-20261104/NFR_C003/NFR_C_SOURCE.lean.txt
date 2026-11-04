import NFR_CHelper
set_option autoImplicit false
noncomputable section
namespace NFR_CHelperBridge
open Aeneas Aeneas.Std Result
abbrev Output := NEU_EmitModel.Output
abbrev Bytes := Array U8 792#usize
abbrev EncodeError := NEU_EmitModel.Error
abbrev ProgramError := AdapterRw.solana_program_error.ProgramError

/-- Exact value-level semantics of the extracted frozen helper. Box allocation
is erased by Aeneas and therefore remains covered by the separate native cut. -/
def run (encoder : Output → Result (core.result.Result Bytes EncodeError)) (r : Output) :
    Result (core.result.Result Bytes ProgramError) := do
  let reply ← encoder r
  match reply with
  | .Ok bytes => ok (.Ok bytes)
  | .Err _ => ok (.Err NFR_CSettlement.invalidReturn)

theorem semantic (encoder : Output → Result (core.result.Result Bytes EncodeError)) (r : Output) :
    NFR_CHelper.terminal_ref encoder r = run encoder r := by
  cases reply : encoder r with
  | fail error =>
    simp only [NFR_CHelper.terminal_ref,NFR_CHelper.terminal_result_bytes_box_v1,run,reply,bind_tc_fail]
  | div =>
    simp only [NFR_CHelper.terminal_ref,NFR_CHelper.terminal_result_bytes_box_v1,run,reply,bind_tc_div]
  | ok answer =>
    cases answer with
    | Ok bytes =>
      rw [NFR_CHelper.accepted encoder r bytes reply]
      simp only [run,reply,bind_tc_ok]
    | Err error =>
      rw [NFR_CHelper.rejected encoder r error reply]
      simp only [run,reply,bind_tc_ok]

/-- The CLOSED encoder bridge is instantiated at the SAME emitted result.
Its statement domain follows from original statement validation. -/
theorem same_emission (s : NEU_EmitModel.Statement)
    (authenticated : NFO_ReadModel.Accepted)
    (same : authenticated.value = AspisR1.S2K.ResultAdmission.value s)
    (valid : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NFR_CHelper.terminal_ref NEY_EmitComposed.encode authenticated.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) :=
  NFR_CHelper.accepted _ _ _ (NFR_CSettlement.reencode_same s authenticated same valid)

#print axioms semantic
#print axioms same_emission
end NFR_CHelperBridge
