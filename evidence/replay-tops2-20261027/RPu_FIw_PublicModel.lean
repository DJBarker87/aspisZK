import RPu_FIw_CoefficientTransport
import RPu_FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_PublicModel
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
abbrev Public := FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := FIq_Native.state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors

def digest (d : Array U32 8#usize) : R0P.Digest K :=
  fun i=>((d.val[i.val]'(by simpa [d.property] using i.isLt)).val : K)
def ofPublic (p : Public) : R0P.Public K where
  variant := FIw_CoefficientTransport.variant p.variant
  anchor := digest p.anchor
  nullifier := digest p.nullifier
  assetId := (p.asset_id.val : K)
  recipient := p.recipient.map digest
  change := digest p.change
  withdrawalAmount := p.withdrawal_amount.map (fun m=>(m.val : K))
  nextPairIndex := p.transition.live_snapshot.next_pair_index.val
  snapshotFrontier := fun i=>digest (p.transition.live_snapshot.frontier.val[i.val]'(by
    simpa [p.transition.live_snapshot.frontier.property] using i.isLt))
  nextRoot := digest p.transition.candidate_afterstate.next_root
  nextFrontier := fun i=>digest (p.transition.candidate_afterstate.next_frontier.val[i.val]'(by
    simpa [p.transition.candidate_afterstate.next_frontier.property] using i.isLt))
def openings (o : Openings) : R0P.Openings K where
  z := fun i=>FIv_NativeArray.value o.z i.val
  succ := fun i=>FIv_NativeArray.value o.succ_z i.val
  xor12 := fun i=>FIv_NativeArray.value o.xor12_z i.val

def selector (s : Selectors) : R0P.Sel K :=
  fun i=>FIv_NativeArray.value s.high (i.val/16)*FIv_NativeArray.value s.low (i.val%16)
end AspisR1.FIw_PublicModel
end
