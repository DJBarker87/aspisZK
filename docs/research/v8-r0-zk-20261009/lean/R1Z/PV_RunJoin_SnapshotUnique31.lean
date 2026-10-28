import R1Z.PV_RunJoin_LateSnapshot31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SnapshotUnique31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22

theorem root [ExternalLinear] (a b : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (left right : pair_forest_copy_builder.CopyRecords) (leafA leafB : Digest)
    (outA outB : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (ha : pair_forest_trace.late_append left a leafA = ok (.Ok outA))
    (hb : pair_forest_trace.late_append right b leafB = ok (.Ok outB))
    (index : a.next_pair_index = b.next_pair_index) (frontier : a.frontier = b.frontier) :
    a.current_root = b.current_root := by
  obtain ⟨rootsA,heA,hrA⟩ := PV_RunJoin_LateSnapshot31.checked left a leafA outA ha
  obtain ⟨rootsB,heB,hrB⟩ := PV_RunJoin_LateSnapshot31.checked right b leafB outB hb
  have roots := Result.ok.inj (heA.symm.trans heB)
  cases roots
  have frame : PV_RunJoin_SnapshotRoot31.read ⟨a.next_pair_index,a.current_root,a.frontier⟩ rootsA =
      PV_RunJoin_SnapshotRoot31.read ⟨b.next_pair_index,b.current_root,b.frontier⟩ rootsA := by
    rw [← index,← frontier]
    exact PV_RunJoin_SnapshotRoot31.frame _ _ _ _ _
  exact core.result.Result.Ok.inj (Result.ok.inj (hrA.symm.trans (frame.trans hrB)))
#print axioms root

theorem sequence [ExternalLinear] (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (out : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok out)) :
    snapshot.sequence = snapshot.next_pair_index := by
  unfold pair_forest_trace.late_append at h
  by_contra different
  have bad : (snapshot.sequence != snapshot.next_pair_index) = true := by simpa using different
  rw [if_pos bad] at h
  cases h
#print axioms sequence
end R1Z.PV_RunJoin_SnapshotUnique31
