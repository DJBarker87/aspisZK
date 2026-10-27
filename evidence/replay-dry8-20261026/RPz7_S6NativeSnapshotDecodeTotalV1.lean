import RPz7_S6NativeSnapshotDecoderPart0FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecodeTotal
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeSnapshotDecoderFactored

@[step] theorem decode_spec (bytes : Slice U8) : decode bytes ⦃ _ => True ⦄ := by
  unfold decode POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*

/-- TOTAL actual native decoder on arbitrary slices, including every rejection path. -/
theorem decode_total (bytes : Slice U8) :
    ∃ result, decode_pool_v1_pair_live_snapshot_v1 bytes=ok result := by
  obtain ⟨result,run,_⟩ := spec_imp_exists (decode_spec bytes)
  exact ⟨result,(decode_source bytes).symm.trans run⟩

#print axioms decode_spec
#print axioms decode_total
end AspisS6NativeSnapshotDecodeTotal
