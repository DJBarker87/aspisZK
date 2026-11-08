import NNH_HostExec
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostOracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

theorem byte (b : Fin 256) :
 decodeByte (NNC_ByteCarriers.nativeByte (UInt8.ofNat b.val)) = b := by
 apply Fin.ext
 change b.val % 256 = b.val
 exact Nat.mod_eq_of_lt b.isLt

theorem flatten_single (message : Bytes) :
 DGP_HostDigest.hostFlatten [LIBB_ProtocolBytes.host message] = message := by
 simp only [DGP_HostDigest.hostFlatten,LIBB_ProtocolBytes.host,
  NNC_ByteCarriers.nativeList,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map]
 induction message with
 | nil => rfl
 | cons b bs ih =>
  change decodeByte (NNC_ByteCarriers.nativeByte (UInt8.ofNat b.val)) :: _ = b :: bs
  rw [byte]
  exact congrArg (List.cons b) ih

theorem singleton_oracle (H : Bytes → State)
 (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (message : Bytes) : LIBB_HashModel.H (DGP_HostDigest.envInst H pda clock r) message = H message := by
 change decodeState (LIB_Env.nativeKey (NNC_ResumeEvents.digest
  (encodeState (H (DGP_HostDigest.hostFlatten [LIBB_ProtocolBytes.host message]))))) = _
 rw [DGP_HostDigest.key_digest,flatten_single,state_roundtrip]
theorem partition_oracle (H : Bytes → State)
 (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (parts : S2Z.Oracle.Parts)
 (partition : LIBB_C04Partition.partition (LIBB_ProtocolBytes.host (flatten parts)) =
  NNC_ResumeEvents.parts parts) :
 LIBB_PartitionEnv.H (DGP_HostDigest.envInst H pda clock r) (flatten parts) = H (flatten parts) := by
 have h := LIBB_PartitionEnv.partition_value (DGP_HostDigest.envInst H pda clock r) parts partition
 change encodeState (LIBB_PartitionEnv.H (DGP_HostDigest.envInst H pda clock r) (flatten parts)) =
  LIB_Env.nativeKey (NNC_ResumeEvents.digest
   (encodeState (H (DGP_HostDigest.hostFlatten (NNC_ResumeEvents.parts parts))))) at h
 rw [DGP_HostDigest.key_digest,DGP_HostDigest.flatten_parts] at h
 have d := congrArg decodeState h
 simpa only [state_roundtrip] using d

theorem node_oracle (H : Bytes → State)
 (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (left right : Array U8 32#usize) :
 LIBB_PartitionEnv.H (DGP_HostDigest.envInst H pda clock r)
  (flatten (MultiproofConePhysicalDigest.parts left right)) =
 H (flatten (MultiproofConePhysicalDigest.parts left right)) :=
 partition_oracle H pda clock r _ (LIBB_FlattenBytes.node left right)

theorem leaf_oracle (H : Bytes → State)
 (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (kind : Usize) (opening : Slice U8) :
 LIBB_PartitionEnv.H (DGP_HostDigest.envInst H pda clock r)
  (flatten (Port4B_LeafCode.input kind opening)) = H (flatten (Port4B_LeafCode.input kind opening)) :=
 partition_oracle H pda clock r _ (LIBB_C04InputPartition.input kind opening)

theorem reader_header {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (pub proof ck : RSL.Bytes) :
 NNH_G1aEnv.header (NNH_HostCtx.envOf c) pub proof ck ↔
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck) =
 some (c.sha256 (NNC_ByteCarriers.protocol proof),c.sha256 (NNC_ByteCarriers.protocol pub)) := by
 unfold NNH_G1aEnv.header
 rw [singleton_oracle,singleton_oracle]

#print axioms partition_oracle
#print axioms node_oracle
#print axioms leaf_oracle
#print axioms reader_header
#print axioms byte
#print axioms flatten_single
#print axioms singleton_oracle
end AspisR1.NNH_HostOracle
end
