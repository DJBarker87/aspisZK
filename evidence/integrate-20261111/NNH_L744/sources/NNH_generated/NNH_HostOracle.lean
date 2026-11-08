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
#print axioms byte
#print axioms flatten_single
#print axioms singleton_oracle
end AspisR1.NNH_HostOracle
end
