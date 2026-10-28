import R1Z.PV_RunJoin_AppendNative17
import R1Z.PV_RunJoin_ParentValue17
import R1Z.PV_RunJoin_OwnedConstructor18
import R1Z.PV_RunJoin_ReconstructWithdrawal1418
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Reconstruct18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_AppendNative17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem withdrawal_suffix13 (frontier : PV_RunJoin_ZeroTree17.Frontier) :
    incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
      ⟨13#usize,20#usize⟩ 1#u64 frontier PV_Src_CanonicalRoots.table withdrawal13 = ok withdrawal20 := by
  rw [incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop]
  obtain ⟨⟨a,b⟩,hn,hv,he⟩ := PV_Src_Forest_BankRange.next_some (⟨13#usize,20#usize⟩ : core.ops.range.Range Usize) (by decide)
  have hs : a = 14#usize := UScalar.eq_of_val_eq hv
  change b = 20#usize at he
  rw [hs,he] at hn
  rw [hn]
  simp only [bind_tc_ok,lift]
  rw [if_pos (by rw [BuilderStdModels.shift64_spec]; decide)]
  rw [index_ok_gen PV_Src_CanonicalRoots.table 13#usize (by decide)]
  simp only [bind_tc_ok]
  change (do
    let p ← format.pool_v1_tree_parent withdrawal13 PV_Src_CanonicalRoots.table.val[13]!
    incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
      ⟨14#usize,20#usize⟩ 1#u64 frontier PV_Src_CanonicalRoots.table p) = _
  have hp : format.pool_v1_tree_parent withdrawal13 PV_Src_CanonicalRoots.table.val[13]! = ok withdrawal14 := by
    apply PV_RunJoin_ParentValue17.source
    · exact PV_Src_CanonicalRoots.canonical ⟨13,by decide⟩
    · intro k hk; interval_cases k <;> decide
    · exact withdrawal_node13
  rw [hp]
  simp only [bind_tc_ok]
  exact withdrawal_suffix14 frontier
#print axioms withdrawal_suffix13
end R1Z.PV_RunJoin_Reconstruct18
