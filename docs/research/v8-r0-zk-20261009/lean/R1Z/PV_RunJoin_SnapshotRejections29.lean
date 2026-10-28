import R1Z.PV_RunJoin_SnapshotDomain29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SnapshotRejections29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder.pool_v1.pair_tree_profile
open R1Z.PV_RunJoin_SnapshotDomain29

theorem zero_binding (s : PoolV1PairLiveSnapshotV1)
    (h : s.pool=zero ∨ s.deployment_domain=zero) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (.Err .ZeroRequiredBinding) := by
  rw [source_result,result,if_pos h]
#print axioms zero_binding

theorem sequence (s : PoolV1PairLiveSnapshotV1)
    (hp : s.pool≠zero) (hd : s.deployment_domain≠zero) (h : s.sequence≠s.next_pair_index) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (.Err .SequenceIndexMismatch) := by
  rw [source_result,result,if_neg (not_or.mpr ⟨hp,hd⟩),if_pos h]
#print axioms sequence

theorem full (s : PoolV1PairLiveSnapshotV1)
    (hp : s.pool≠zero) (hd : s.deployment_domain≠zero) (hs : s.sequence=s.next_pair_index)
    (h : 1048576 ≤ s.next_pair_index.val) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (.Err .TreeFull) := by
  rw [source_result,result,if_neg (not_or.mpr ⟨hp,hd⟩),if_neg (not_not.mpr hs),if_pos h]
#print axioms full

theorem digest (s : PoolV1PairLiveSnapshotV1)
    (hp : s.pool≠zero) (hd : s.deployment_domain≠zero) (hs : s.sequence=s.next_pair_index)
    (hn : s.next_pair_index.val < 1048576)
    (bad : ¬(R0Z.WriterRefine.Canon8 s.current_root ∧
      ∀ l : Fin 20, R0Z.WriterRefine.Canon8 s.frontier.val[l.val]!)) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (.Err .NonCanonicalDigest) := by
  rw [source_result,result,if_neg (not_or.mpr ⟨hp,hd⟩),if_neg (not_not.mpr hs),
    if_neg (Nat.not_le.mpr hn),if_neg bad]
#print axioms digest
end R1Z.PV_RunJoin_SnapshotRejections29
