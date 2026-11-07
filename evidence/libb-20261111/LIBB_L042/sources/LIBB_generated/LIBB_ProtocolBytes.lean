import LIB_Env
set_option autoImplicit false
namespace LIBB_ProtocolBytes
open Aeneas Aeneas.Std
abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
/-- Convert protocol bytes back to the shared RSL byte carrier. -/
def host (bs : Bytes) : RSL.Bytes := bs.map (fun b => UInt8.ofNat b.val)

theorem host_native (bs : List U8) :
 host (AspisR1.MultiproofConeCanonical.bytesOf bs) = NNC_ByteCarriers.host bs := by
 simp only [host,AspisR1.MultiproofConeCanonical.bytesOf,NNC_ByteCarriers.host,List.map_map]
 apply List.map_congr_left
 intro x _
 apply UInt8.toBitVec_inj.mp
 change BitVec.ofNat 8 x.bv.toNat = x.bv
 simp

theorem host_protocol (bs : RSL.Bytes) : host (NNC_ByteCarriers.protocol bs) = bs :=
 (host_native (NNC_ByteCarriers.nativeList bs)).trans (NNC_ByteCarriers.host_native bs)
#print axioms host_native
#print axioms host_protocol
end LIBB_ProtocolBytes
