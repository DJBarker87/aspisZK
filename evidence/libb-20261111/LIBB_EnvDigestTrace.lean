import LIBB_PartitionEnv
import LIBB_C04RichTrace
set_option autoImplicit false
noncomputable section
namespace LIBB_EnvDigestTrace
open Aeneas Aeneas.Std AspisR1
/-- SAME node part list and returned bytes, without repartitioning assumptions. -/
theorem node (env : RSL.Env) (left right : Array U8 32#usize) :
 (LIBB_PartitionEnv.digest env).digest () (MultiproofConePhysicalDigest.parts left right) =
 .ok (AspisV8R19.SqueezeOracleBridge.encodeState (LIBB_PartitionEnv.H env
  (AspisV8R19.SqueezeOracleBridge.flatten (MultiproofConePhysicalDigest.parts left right)))) := by
 rw [LIBB_PartitionEnv.digest_value,LIBB_PartitionEnv.partition_value env _ (LIBB_FlattenBytes.node left right)]

theorem leaf (env : RSL.Env) (kind : Usize) (opening : Slice U8) :
 (LIBB_PartitionEnv.digest env).digest () (Port4B_LeafCode.input kind opening) =
 .ok (AspisV8R19.SqueezeOracleBridge.encodeState (LIBB_PartitionEnv.H env
  (AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input kind opening)))) := by
 rw [LIBB_PartitionEnv.digest_value,LIBB_PartitionEnv.leaf_value]

/-- Every graph query retains the original actual partition. The reply law
is explicit here; a native association must derive it from its child root. -/
theorem event (env : RSL.Env) (parts : Slice (Slice U8))
 (partition : LIBB_C04Partition.partition (LIBB_ProtocolBytes.host
  (AspisV8R19.SqueezeOracleBridge.flatten parts))=NNC_ResumeEvents.parts parts) :
 LIBB_C04LogGraph.render [(AspisV8R19.SqueezeOracleBridge.flatten parts,
  LIBB_PartitionEnv.H env (AspisV8R19.SqueezeOracleBridge.flatten parts))] =
 [RSL.Event.digest (NNC_ResumeEvents.parts parts) (env.sha256 (NNC_ResumeEvents.parts parts))] := by
 change [RSL.Event.digest _ _]=_
 rw [partition,LIBB_PartitionEnv.partition_value env parts partition]
 rw [LIB_Env.digest_event]
#print axioms node
#print axioms leaf
#print axioms event
end LIBB_EnvDigestTrace
end
