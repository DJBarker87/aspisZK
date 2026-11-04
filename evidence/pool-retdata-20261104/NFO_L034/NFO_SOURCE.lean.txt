import NFO_ReadModel
import NFO_PoolReturnData
import NFO_ReadAccepted
import NFO_RawDecode
import NFO_M31Roundtrip
import NFO_HeaderWrites
import NFO_ResultLayout
import NFO_FlatMapInjective
import NFO_U64Roundtrip
import NFO_AfterstateInjective
import NFO_ResultInjective
import NFO_DecodeOracle
import NFO_DecodeReject
import NFO_PacketDecoder
import NFO_AcceptedAssociation
import NFO_DecodeErrors
import NFO_PacketAccepted
set_option autoImplicit false
noncomputable section
namespace NFO_Final
open Aeneas Aeneas.Std Result
/-- This raw accepted-inverse remains OPEN. Reduction to it does not discharge it. -/
def RawInverse : Prop := ∀ (bytes : Array U8 792#usize) value,
  NFO_RawDecode.decode (Array.to_slice bytes) = ok (.Ok value) →
  NFO_ResultLayout.bytes value = bytes

theorem codec_iff_raw : NFO_AcceptedAssociation.AcceptedCodec ↔ RawInverse := by
  constructor
  · intro codec bytes value decoded
    apply Subtype.ext
    apply codec bytes.val value bytes.property
    exact (NFO_PacketDecoder.on_packet bytes.val bytes.property).trans decoded
  · intro raw bytes value width decoded
    have success := (NFO_PacketDecoder.on_packet bytes width).symm.trans decoded
    exact congrArg Subtype.val (raw ⟨bytes,width⟩ value success)
#print axioms codec_iff_raw
end NFO_Final
