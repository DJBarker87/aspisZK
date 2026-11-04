import NEU_DecoderProjections
set_option autoImplicit false
namespace NEX_BoxValueExt
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Late := pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev Snapshot := pair_tree_profile.PoolV1PairLiveSnapshotV1

/-- Reuse the already audited complete common projection family by embedding
both late values at the same untouched outer record. -/
theorem late (base : Common) (a b : Late)
    (point : ∀ slot i j k,
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon {base with lane_transition:=a}) slot i j k =
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon {base with lane_transition:=b}) slot i j k) : a=b := by
  have same := NEU_DecoderProjections.common_ext {base with lane_transition:=a} {base with lane_transition:=b} point
  exact congrArg (fun c : Common => c.lane_transition) same

/-- Same embedding specializes the complete field family to the live snapshot. -/
theorem snapshot (base : Common) (a b : Snapshot)
    (point : ∀ slot i j k,
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon
        {base with lane_transition:={base.lane_transition with live_snapshot:=a}}) slot i j k =
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon
        {base with lane_transition:={base.lane_transition with live_snapshot:=b}}) slot i j k) : a=b := by
  have same := NEU_DecoderProjections.common_ext
    {base with lane_transition:={base.lane_transition with live_snapshot:=a}}
    {base with lane_transition:={base.lane_transition with live_snapshot:=b}} point
  exact congrArg (fun c : Common => c.lane_transition.live_snapshot) same

#print axioms late
#print axioms snapshot
end NEX_BoxValueExt
