import LIBB_HashModel
import LIBB_C04InputPartition
import LIBB_FlattenBytes
set_option autoImplicit false
noncomputable section
namespace LIBB_PartitionEnv
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- C04 model addresses retain their original physical hashv partition.
Resume calls the actual partitioned Env oracle directly. No invariance of an
arbitrary Env.sha256 under repartitioning is assumed. -/
def H (env : RSL.Env) (message : Bytes) : State :=
 LIBB_HashModel.state (env.sha256 (LIBB_C04Partition.partition (LIBB_ProtocolBytes.host message)))
def digest (env : RSL.Env) : VTop_Stages.aspis_core.digest.Digest32 Unit :=
 ⟨(LIBB_HashModel.digest env).coremarkerCopyInst,fun _ parts => LIB_Env.hashv env parts⟩

theorem digest_value (env : RSL.Env) (parts : Slice (Slice U8)) :
 (digest env).digest () parts = .ok (LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts parts))) := rfl

theorem partition_value (env : RSL.Env) (parts : Slice (Slice U8))
 (partition : LIBB_C04Partition.partition (LIBB_ProtocolBytes.host
  (AspisV8R19.SqueezeOracleBridge.flatten parts)) = NNC_ResumeEvents.parts parts) :
 AspisV8R19.SqueezeOracleBridge.encodeState (H env (AspisV8R19.SqueezeOracleBridge.flatten parts)) =
 LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts parts)) := by
 unfold H
 rw [partition]
 unfold LIBB_HashModel.state
 exact AspisV8R19.SqueezeOracleBridge.array_roundtrip _

theorem leaf_value (env : RSL.Env) (kind : Usize) (opening : Slice U8) :
 AspisV8R19.SqueezeOracleBridge.encodeState
  (H env (AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input kind opening))) =
 LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts (Port4B_LeafCode.input kind opening))) :=
 partition_value env _ (LIBB_C04InputPartition.input kind opening)
#print axioms digest_value
#print axioms partition_value
#print axioms leaf_value
end LIBB_PartitionEnv
end
