import R1Z.PV_RunJoin_AppendNative17
import R1Z.PV_RunJoin_ParentValue17
import R1Z.PV_RunJoin_OwnedConstructor18
import R1Z.PV_RunJoin_ReconstructTransfer0118
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Reconstruct18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_AppendNative17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem transfer_suffix0 (frontier : PV_RunJoin_ZeroTree17.Frontier) (hf : frontier.val[0]! = transfer0) :
    incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
      ⟨0#usize,20#usize⟩ 1#u64 frontier PV_Src_CanonicalRoots.table PV_Src_CanonicalRoots.table.val[0]! = ok transfer20 := by
  rw [incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop]
  obtain ⟨⟨a,b⟩,hn,hv,he⟩ := PV_Src_Forest_BankRange.next_some (⟨0#usize,20#usize⟩ : core.ops.range.Range Usize) (by decide)
  have hs : a = 1#usize := UScalar.eq_of_val_eq hv
  change b = 20#usize at he
  rw [hs,he] at hn
  rw [hn]
  simp only [bind_tc_ok,lift]
  rw [if_neg (by rw [BuilderStdModels.shift64_spec]; decide)]
  rw [index_ok_gen frontier 0#usize (by decide)]
  simp only [bind_tc_ok]
  change (do
    let p ← format.pool_v1_tree_parent frontier.val[0]! PV_Src_CanonicalRoots.table.val[0]!
    incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
      ⟨1#usize,20#usize⟩ 1#u64 frontier PV_Src_CanonicalRoots.table p) = _
  rw [hf]
  have hp : format.pool_v1_tree_parent transfer0 PV_Src_CanonicalRoots.table.val[0]! = ok transfer1 := by
    apply PV_RunJoin_ParentValue17.source
    · exact PV_Src_CanonicalRoots.canonical ⟨0,by decide⟩
    · intro k hk; interval_cases k <;> decide
    · exact transfer_node0
  rw [hp]
  simp only [bind_tc_ok]
  exact transfer_suffix1 frontier
#print axioms transfer_suffix0
end R1Z.PV_RunJoin_Reconstruct18
