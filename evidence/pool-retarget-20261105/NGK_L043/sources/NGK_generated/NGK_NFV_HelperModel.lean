import Lean
import NGK_NFR_CHelperBridge

set_option autoImplicit false
noncomputable section
namespace NGK_NFV_HelperModel
open Aeneas Aeneas.Std Result
abbrev Output := NFY_NEU_EmitModel.Output
abbrev Bytes := NGK_NFR_CHelperBridge.Bytes
abbrev Error := NGK_NFR_CHelperBridge.EncodeError
abbrev ProgramError := NGK_NFR_CHelperBridge.ProgramError
inductive Call where
  | encode (value : Output)
  | allocate (bytes : Bytes)

def run (encoder : Output → Result (core.result.Result Bytes Error)) (r : Output) :
    Result (core.result.Result Bytes ProgramError × List Call) := do
  let answer ← encoder r
  match answer with
  | .Err _ => ok (.Err NGK_NFR_CSettlement.invalidReturn,[.encode r])
  | .Ok bytes => ok (.Ok bytes,[.encode r,.allocate bytes])

theorem success (encoder : Output → Result (core.result.Result Bytes Error))
    (r : Output) (bytes : Bytes) (encoded : encoder r = ok (.Ok bytes)) :
    run encoder r = ok (.Ok bytes,[.encode r,.allocate bytes]) := by
  simp only [run,encoded,bind_tc_ok]
#print axioms success

theorem rejected (encoder : Output → Result (core.result.Result Bytes Error))
    (r : Output) (error : Error) (encoded : encoder r = ok (.Err error)) :
    run encoder r = ok (.Err NGK_NFR_CSettlement.invalidReturn,[.encode r]) := by
  simp only [run,encoded,bind_tc_ok]
#print axioms rejected

/-- Ghost call observations erase to the already extracted helper semantics;
allocation remains present in the observation trace, and errors allocate nothing. -/
theorem erase (encoder : Output → Result (core.result.Result Bytes Error)) (r : Output) :
    (do let observed ← run encoder r; ok observed.1) =
      NGK_NFR_CHelper.terminal_ref encoder r := by
  rw [NGK_NFR_CHelperBridge.semantic]
  cases h : encoder r with
  | fail e => simp only [run,NGK_NFR_CHelperBridge.run,h,bind_tc_fail]
  | div => simp only [run,NGK_NFR_CHelperBridge.run,h,bind_tc_div]
  | ok answer =>
    cases answer <;> simp only [run,NGK_NFR_CHelperBridge.run,h,bind_tc_ok]
#print axioms erase

/-- The original validated statement discharges the CLOSED encoder's domain on
this same authenticated value, without an extra encoder-domain hypothesis. -/
theorem same_emission (s : NFY_NEU_EmitModel.Statement) (authenticated : NGK_NFO_ReadModel.Accepted)
    (same : authenticated.value = AspisR1.S2K.ResultAdmission.value s)
    (valid : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    run NFY_NEY_EmitComposed.encode authenticated.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s),
        [.encode authenticated.value,.allocate (AspisR1.S2K.ResultPayload.bytes s)]) := by
  exact success _ _ _ (NGK_NFR_CSettlement.reencode_same s authenticated same valid)
#print axioms same_emission
end NGK_NFV_HelperModel

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
