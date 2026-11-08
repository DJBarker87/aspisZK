import NNU_MerkleSlots
import NNH_NativeOracleReply
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleDigest
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem node (env : RSL.Env) (left right : Array U8 32#usize) :
 (LIBB_PartitionEnv.digest env).digest () (MultiproofConePhysicalDigest.parts left right) =
 .ok (MultiproofConePhysicalTransport.rawOracle (LIBB_PartitionEnv.H env)
  (MultiproofConePhysicalDigest.parts left right)) := by
 rw [LIBB_PartitionEnv.digest_value]
 unfold MultiproofConePhysicalTransport.rawOracle
 rw [LIBB_PartitionEnv.partition_value env _ (LIBB_FlattenBytes.node left right)]

theorem leaf (env : RSL.Env) (kind : Usize) (opening : Slice U8) :
 (LIBB_PartitionEnv.digest env).digest () (Port4B_LeafCode.input kind opening) =
 .ok (MultiproofConePhysicalTransport.rawOracle (LIBB_PartitionEnv.H env)
  (Port4B_LeafCode.input kind opening)) := by
 rw [LIBB_PartitionEnv.digest_value]
 unfold MultiproofConePhysicalTransport.rawOracle
 rw [LIBB_PartitionEnv.leaf_value]
#print axioms node
#print axioms leaf
end AspisR1.NNU_MerkleDigest
end
