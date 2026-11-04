import Lean
import NGK_NFO_ReadModel
import NGK_NFO_PoolReturnData
import NGK_NFO_ReadAccepted
import NGK_NFO_RawDecode
import NGK_NFO_M31Roundtrip
import NGK_NFO_HeaderWrites
import NGK_NFO_ResultLayout
import NGK_NFO_FlatMapInjective
import NGK_NFO_U64Roundtrip
import NGK_NFO_AfterstateInjective
import NGK_NFO_ResultInjective
import NGK_NFO_DecodeOracle
import NGK_NFO_DecodeReject
import NGK_NFO_PacketDecoder
import NGK_NFO_AcceptedAssociation
import NGK_NFO_DecodeErrors
import NGK_NFO_PacketAccepted

set_option autoImplicit false
noncomputable section
namespace NGK_NFO_Final
open Aeneas Aeneas.Std Result
/-- This raw accepted-inverse remains OPEN. Reduction to it does not discharge it. -/
def RawInverse : Prop := ∀ (bytes : Array U8 792#usize) value,
  NGK_NFO_RawDecode.decode (Array.to_slice bytes) = ok (.Ok value) →
  NGK_NFO_ResultLayout.bytes value = bytes

theorem codec_iff_raw : NGK_NFO_AcceptedAssociation.AcceptedCodec ↔ RawInverse := by
  constructor
  · intro codec bytes value decoded
    apply Subtype.ext
    apply codec bytes.val value bytes.property
    exact (NGK_NFO_PacketDecoder.on_packet bytes.val bytes.property).trans decoded
  · intro raw bytes value width decoded
    have success := (NGK_NFO_PacketDecoder.on_packet bytes width).symm.trans decoded
    exact congrArg Subtype.val (raw ⟨bytes,width⟩ value success)
#print axioms codec_iff_raw
end NGK_NFO_Final

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
