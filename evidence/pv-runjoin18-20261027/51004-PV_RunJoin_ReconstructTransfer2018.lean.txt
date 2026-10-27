import R1Z.PV_RunJoin_AppendNative17
import R1Z.PV_RunJoin_ParentValue17
import R1Z.PV_RunJoin_OwnedConstructor18
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Reconstruct18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_AppendNative17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
abbrev Frontier := Array (Array U32 8#usize) 20#usize
theorem transfer_suffix20 (frontier : Frontier) :
    incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
      ⟨20#usize,20#usize⟩ 1#u64 frontier PV_Src_CanonicalRoots.table transfer20 = ok transfer20 := by
  rw [incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop]
  with_unfolding_all rfl
#print axioms transfer_suffix20
end R1Z.PV_RunJoin_Reconstruct18
