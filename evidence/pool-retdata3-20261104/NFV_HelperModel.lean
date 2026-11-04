import NFR_CHelperBridge
set_option autoImplicit false
noncomputable section
namespace NFV_HelperModel
open Aeneas Aeneas.Std Result
abbrev Output := NEU_EmitModel.Output
abbrev Bytes := NFR_CHelperBridge.Bytes
abbrev Error := NFR_CHelperBridge.EncodeError
abbrev ProgramError := NFR_CHelperBridge.ProgramError
inductive Call where
  | encode (value : Output)
  | allocate (bytes : Bytes)

def run (encoder : Output → Result (core.result.Result Bytes Error)) (r : Output) :
    Result (core.result.Result Bytes ProgramError × List Call) := do
  let answer ← encoder r
  match answer with
  | .Err _ => ok (.Err NFR_CSettlement.invalidReturn,[.encode r])
  | .Ok bytes => ok (.Ok bytes,[.encode r,.allocate bytes])

theorem success (encoder : Output → Result (core.result.Result Bytes Error))
    (r : Output) (bytes : Bytes) (encoded : encoder r = ok (.Ok bytes)) :
    run encoder r = ok (.Ok bytes,[.encode r,.allocate bytes]) := by
  simp only [run,encoded,bind_tc_ok]
#print axioms success

theorem rejected (encoder : Output → Result (core.result.Result Bytes Error))
    (r : Output) (error : Error) (encoded : encoder r = ok (.Err error)) :
    run encoder r = ok (.Err NFR_CSettlement.invalidReturn,[.encode r]) := by
  simp only [run,encoded,bind_tc_ok]
#print axioms rejected

/-- Ghost call observations erase to the already extracted helper semantics;
allocation remains present in the observation trace, and errors allocate nothing. -/
theorem erase (encoder : Output → Result (core.result.Result Bytes Error)) (r : Output) :
    (do let observed ← run encoder r; ok observed.1) =
      NFR_CHelper.terminal_ref encoder r := by
  rw [NFR_CHelperBridge.semantic]
  cases h : encoder r with
  | fail e => simp only [run,NFR_CHelperBridge.run,h,bind_tc_fail]
  | div => simp only [run,NFR_CHelperBridge.run,h,bind_tc_div]
  | ok answer =>
    cases answer <;> simp only [run,NFR_CHelperBridge.run,h,bind_tc_ok]
#print axioms erase

/-- The original validated statement discharges the CLOSED encoder's domain on
this same authenticated value, without an extra encoder-domain hypothesis. -/
theorem same_emission (s : NEU_EmitModel.Statement) (authenticated : NFO_ReadModel.Accepted)
    (same : authenticated.value = AspisR1.S2K.ResultAdmission.value s)
    (valid : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    run NEY_EmitComposed.encode authenticated.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s),
        [.encode authenticated.value,.allocate (AspisR1.S2K.ResultPayload.bytes s)]) := by
  exact success _ _ _ (NFR_CSettlement.reencode_same s authenticated same valid)
#print axioms same_emission
end NFV_HelperModel
