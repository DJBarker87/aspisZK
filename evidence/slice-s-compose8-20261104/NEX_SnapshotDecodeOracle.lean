import S6NativeSnapshotDecoderFactoredV1
set_option autoImplicit false
noncomputable section
namespace NEX_SnapshotDecodeOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
/-- Reuse the existing factored model law; the excluded deep clone is not credit.
Native oracle cuts, caller domains and physical frames are separate checks. -/
abbrev run := AspisS6NativeSnapshotDecoderFactored.decode
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run bytes,state,([] : List Unit)) =
    (pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes,state,[]) := by
  exact congrArg (fun r => (r,state,([] : List Unit))) (AspisS6NativeSnapshotDecoderFactored.decode_source bytes)
#print axioms result_state_effects
#print axioms AspisS6NativeSnapshotDecoderFactored.decode_source
end NEX_SnapshotDecodeOracle
