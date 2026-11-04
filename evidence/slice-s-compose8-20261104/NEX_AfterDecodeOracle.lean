import NED_SubtreeComposition
set_option autoImplicit false
noncomputable section
namespace NEX_AfterDecodeOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
/-- Reuse the existing factored model law; the excluded deep clone is not credit.
Native oracle cuts, caller domains and physical frames are separate checks. -/
abbrev run := NBN_AfterstateDecoderDependency.run (fun b => ok (NBP_DigestDecode.decoded b))
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run bytes,state,([] : List Unit)) =
    (pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes,state,[]) := by
  exact congrArg (fun r => (r,state,([] : List Unit))) (NED_SubtreeComposition.after_decode bytes)
#print axioms result_state_effects
#print axioms NED_SubtreeComposition.after_decode
end NEX_AfterDecodeOracle
