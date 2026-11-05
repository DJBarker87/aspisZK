import Lean
import NFY_Part030

set_option autoImplicit false
noncomputable section
namespace NGF_NEX_AfterDecodeOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
/-- Reuse the existing factored model law; the excluded deep clone is not credit.
Native oracle cuts, caller domains and physical frames are separate checks. -/
abbrev run := NFY_NBN_AfterstateDecoderDependency.run (fun b => ok (NFY_NBP_DigestDecode.decoded b))
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run bytes,state,([] : List Unit)) =
    (pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes,state,[]) := by
  exact congrArg (fun r => (r,state,([] : List Unit))) (NFY_NED_SubtreeComposition.after_decode bytes)
#print axioms result_state_effects
#print axioms NFY_NED_SubtreeComposition.after_decode
end NGF_NEX_AfterDecodeOracle

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
