import LIBB_AccountDecoderReuse
import NND_CheckpointCarrier
set_option autoImplicit false
namespace LIBB_AccountCarriers
open Aeneas Aeneas.Std
/-- Nat conversions in the sibling decoder and bit-pattern conversions in
LIB preserve all bit patterns, with no canonicality premise. -/
theorem byte : NMX_R2_Carrier.byte = NND_Carrier.byte := by
 funext x
 apply UInt8.toBitVec_inj.mp
 change BitVec.ofNat 8 x.bv.toNat = x.bv
 simp

theorem word : NMX_R2_Carrier.word = NND_Carrier.word := by
 funext x
 apply UInt32.toBitVec_inj.mp
 change BitVec.ofNat 32 x.bv.toNat = x.bv
 simp

theorem long : NMX_R2_Carrier.long = NND_Carrier.slot := by
 funext x
 apply UInt64.toBitVec_inj.mp
 change BitVec.ofNat 64 x.bv.toNat = x.bv
 simp

theorem bytes (b : Slice U8) : NMX_R2_Carrier.bytes b = NND_Carrier.bytes b := by
 simp only [NMX_R2_Carrier.bytes,NND_Carrier.bytes,byte]

theorem master (m : NMX_OwnedPackets.Master) : NMX_R2_Carrier.master m = NND_Carrier.master m := by
 simp only [NMX_R2_Carrier.master,NND_Carrier.master,NMX_R2_Carrier.identity,
   NND_Carrier.poolIdentity,NMX_R2_Carrier.policy,NND_Carrier.policy,
   NMX_R2_Carrier.key,NND_Carrier.key,NND_Carrier.slots,byte,word,long]

theorem checkpoint (c : NMX_OwnedPackets.Checkpoint) :
 NMX_R2_Carrier.checkpoint c = NND_Carrier.checkpoint c := by
 simp only [NMX_R2_Carrier.checkpoint,NND_Carrier.checkpoint,NMX_R2_Carrier.key,
  NND_Carrier.key,NMX_R2_Carrier.digest,NND_Carrier.digest,NND_Carrier.slots,
  byte,word,long]
#print axioms byte
#print axioms word
#print axioms long
#print axioms bytes
#print axioms master
#print axioms checkpoint
end LIBB_AccountCarriers
