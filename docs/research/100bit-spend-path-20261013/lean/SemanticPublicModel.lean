import OccupancyGeneratedSlice
import OccupancyExpectedBridge
import ExtractedMaskQM31Exact
import R0P.Core

/-! One exact-field interpretation of the actual retained SemanticPublic.
This definition casts source words; canonicality is a separate input property. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicModel
open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic

def digest (d : Array field.M31 8#usize) : R0P.Digest ExactQM :=
  fun i => ((d.val[i.val]'(by simpa [d.property] using i.isLt)).val : ExactQM)

def exactPublic (public1 : Public) : R0P.Public ExactQM where
  variant := AspisR1.OccupancyExpectedBridge.modelVariant public1.variant
  anchor := digest public1.anchor
  nullifier := digest public1.nullifier
  assetId := (public1.asset_id.val : ExactQM)
  recipient := public1.recipient.map digest
  change := digest public1.change
  withdrawalAmount := public1.withdrawal_amount.map (fun m => (m.val : ExactQM))
  nextPairIndex := public1.transition.live_snapshot.next_pair_index.val
  snapshotFrontier := fun i => digest (public1.transition.live_snapshot.frontier.val[i.val]'(by
    simpa [public1.transition.live_snapshot.frontier.property] using i.isLt))
  nextRoot := digest public1.transition.candidate_afterstate.next_root
  nextFrontier := fun i => digest (public1.transition.candidate_afterstate.next_frontier.val[i.val]'(by
    simpa [public1.transition.candidate_afterstate.next_frontier.property] using i.isLt))

end AspisR1.SemanticPublicModel
