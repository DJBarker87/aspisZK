import LIBC_CohortHash
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_PartitionFinding
open Aeneas Aeneas.Std
/-- Empty openings are outside the reached C04 leaf domain. The unrestricted
NodeLeaf.leaf interface nevertheless quantifies over them. LIBC's split does
not reconstruct their physical hashv partition. -/
theorem empty_leaf_partition :
 let opening : Slice U8 := ⟨[],by simp⟩
 let input := Port4B_LeafCode.input 0#usize opening
 LIBC_HashPartitions.split (LIBC_CohortHash.host
  (AspisV8R19.SqueezeOracleBridge.flatten input)) ≠ NNC_ResumeEvents.parts input := by
 decide
#print axioms empty_leaf_partition
end AspisR1.NNX_PartitionFinding
end
