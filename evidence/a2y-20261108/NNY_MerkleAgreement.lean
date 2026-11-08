import NNU_MerkleLeaf
import NNU_MerkleNode
import NNU_MerkleEnvironment
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Agreement only on the C04 binary-node and leaf request shapes. -/
structure NodeLeaf (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → State) : Prop where
 node : ∀ left right : Array U8 32#usize,
  D.digest () (MultiproofConePhysicalDigest.parts left right) =
   ok (MultiproofConePhysicalTransport.rawOracle H (MultiproofConePhysicalDigest.parts left right))
 leaf : ∀ (kind : Usize) (opening : Slice U8),
  D.digest () (Port4B_LeafCode.input kind opening) =
   ok (MultiproofConePhysicalTransport.rawOracle H (Port4B_LeafCode.input kind opening))
def refDigest (D : VTop_Stages.aspis_core.digest.Digest32 Unit) :=
 Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)
/-- Total auxiliary oracle; no equation on arbitrary D requests is assumed. -/
def totalDigest (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State) :
 MultiproofConeRef.aspis_core.digest.Digest32 Unit :=
 {refDigest D with digest := fun _ parts => ok (MultiproofConePhysicalTransport.rawOracle H parts)}
theorem total (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State) :
 MultiproofConeNodeDomain.HashTotal (totalDigest D H) () := fun _ => ⟨_,rfl⟩
theorem node (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (s : MultiproofConeRef.reference.Scratch)
 (physical : Slice U8) (i w : Usize) :
 MultiproofConeRef.reference.binary_step (refDigest D) () s physical i w =
 MultiproofConeRef.reference.binary_step (totalDigest D H) () s physical i w := by
 have left := NNU_MerkleNode.node (refDigest D) ()
  (MultiproofConePhysicalTransport.rawOracle H) agree.node s physical i w
 have right := NNU_MerkleNode.node (totalDigest D H) ()
  (MultiproofConePhysicalTransport.rawOracle H) (fun _ _ => rfl) s physical i w
 exact left.symm.trans right
theorem leaf (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (kind : Usize) (opening : Slice U8)
 (len : opening.val.length=832) :
 Port4B_LeafCode.native (VTop_Checkpoint.digest D) () kind opening =
 ok (MultiproofConePhysicalTransport.rawOracle H (Port4B_LeafCode.input kind opening)) := by
 rw [Port4B_LeafCode.native,(Port4B_LeafCode.code_exact _ () kind opening len []).1]
 exact agree.leaf kind opening
theorem tx2 (env : RSL.Env) : NodeLeaf (LIBB_PartitionEnv.digest env) (LIBB_PartitionEnv.H env) :=
 ⟨NNU_MerkleDigest.node env,NNU_MerkleDigest.leaf env⟩
#print axioms total
#print axioms node
#print axioms leaf
#print axioms tx2
end AspisR1.NNY_MerkleShared
end
