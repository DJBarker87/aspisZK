import NNU_MerkleDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleLeaf
open Aeneas Aeneas.Std Result
/-- Pointwise at the reached leaf request, with no all-partitions law. -/
theorem source (env : RSL.Env) (kind : Usize) (opening : Slice U8)
 (len : opening.val.length=832) :
 Port4B_LeafCode.native (LIBB_PartitionEnv.digest env) () kind opening =
 .ok (MultiproofConePhysicalTransport.rawOracle (LIBB_PartitionEnv.H env)
  (Port4B_LeafCode.input kind opening)) := by
 rw [Port4B_LeafCode.native, (Port4B_LeafCode.code_exact _ () kind opening len []).1]
 exact NNU_MerkleDigest.leaf env kind opening
#print axioms source
end AspisR1.NNU_MerkleLeaf
end
