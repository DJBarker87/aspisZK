import R1Z.PV_CB_Op229Types
import R1Z.PDict_FinalTypes
set_option autoImplicit false
namespace R1Z.PV_CB_Op229Transport
open Aeneas Aeneas.Std ProverRwFull
abbrev native := PDict_FinalTypes.native
abbrev After := PDict_StatementTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev Snap := ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Late (base : ExternalTypes) :=
  @ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (native base)
abbrev SourceAfter := PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev SourceSnap := PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev SourceLate := PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
def after (x : After) : SourceAfter := ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def unafter (x : SourceAfter) : After := ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def snapshot (x : Snap) : SourceSnap :=
  ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
def unsnapshot (x : SourceSnap) : Snap :=
  ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
def encode (base : ExternalTypes) (x : Late base) : SourceLate := by
  letI : ExternalTypes := native base
  exact ⟨snapshot x.live_snapshot,after x.candidate_afterstate⟩
def decode (base : ExternalTypes) (x : SourceLate) : Late base := by
  letI : ExternalTypes := native base
  exact ⟨unsnapshot x.live_snapshot,unafter x.candidate_afterstate⟩
end R1Z.PV_CB_Op229Transport
