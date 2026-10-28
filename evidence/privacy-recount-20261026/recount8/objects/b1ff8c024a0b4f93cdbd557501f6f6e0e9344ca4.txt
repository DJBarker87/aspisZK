import R1Z.PV_RDCD_V246Raw
import R1Z.PV_CB_Op229Funs
import R1Z.PV_RDCD_SliceArrayBinding
set_option autoImplicit false
namespace R1Z.PV_RDCD_StatementBridge
open Aeneas Aeneas.Std Result
abbrev OldAfter := PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev NewAfter := PV_RDCD_V246.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev OldSnap := PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev NewSnap := PV_RDCD_V246.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev OldLate := PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev NewLate := PV_RDCD_V246.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

def after (a : OldAfter) : NewAfter := ⟨a.next_pair_index,a.next_root,a.next_frontier⟩
def unafter (a : NewAfter) : OldAfter := ⟨a.next_pair_index,a.next_root,a.next_frontier⟩
def snapshot (a : OldSnap) : NewSnap :=
  ⟨a.pool,a.deployment_domain,a.sequence,a.next_pair_index,a.current_root,a.frontier⟩
def unsnapshot (a : NewSnap) : OldSnap :=
  ⟨a.pool,a.deployment_domain,a.sequence,a.next_pair_index,a.current_root,a.frontier⟩
def encode (a : OldLate) : NewLate := ⟨snapshot a.live_snapshot,after a.candidate_afterstate⟩
def decode (a : NewLate) : OldLate := ⟨unsnapshot a.live_snapshot,unafter a.candidate_afterstate⟩

theorem roundtrip (a : OldLate) : decode (encode a) = a := by
  cases a with | mk s a => cases s; cases a; rfl
theorem inverse_roundtrip (a : NewLate) : encode (decode a) = a := by
  cases a with | mk s a => cases s; cases a; rfl
/-- Same complete Result on all raw carriers, including noncanonical M31 words. -/
theorem source (a b : OldLate) :
    PV_RDCD_V246.public_eq (encode a) (encode b) =
    PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq a b := rfl
#print axioms roundtrip
#print axioms inverse_roundtrip
#print axioms source
end R1Z.PV_RDCD_StatementBridge
