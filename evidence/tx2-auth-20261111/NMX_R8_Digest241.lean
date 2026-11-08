import NMX_R4_NMSCarrier
import NMX_R8_Std241
import LIBB_PartitionEnv
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Digest241
open Aeneas Aeneas.Std Result AdapterRw

theorem key (k : RSL.B32) : NMX_R2_InverseBytes.fromKey k = LIB_Env.nativeKey k := by
 apply NMS_R2N_RSLScalars.b32_injective
 have left : NMS_R2N_RSLScalars.b32 (NMX_R2_InverseBytes.fromKey k) = k := by
   rw [NMX_R4_NMSCarrier.key]
   exact NMX_R2_InverseBytes.key_roundtrip k
 exact left.trans (LIB_Env.key_roundtrip k).symm

theorem parts (p : Slice (Slice U8)) : p.val.map NMX_R2_Carrier.bytes = NNC_ResumeEvents.parts p := by
 have each : NMX_R2_Carrier.bytes = (fun s : Slice U8 => NNC_ByteCarriers.host s.val) := by
  funext s
  simp only [NMX_R2_Carrier.bytes,LIBB_AccountCarriers.byte,NNC_ByteCarriers.host]
  rfl
 change p.val.map NMX_R2_Carrier.bytes = p.val.map (fun s => NNC_ByteCarriers.host s.val)
 rw [each]

theorem descriptor (env : RSL.Env) (p : Slice (Slice U8)) :
 (SolanaDigest.Insts.Aspis_coreDigestDigest32 (NMX_R8_Std241.ops env)).digest () p =
 (LIBB_PartitionEnv.digest env).digest () p := by
 rw [LIBB_PartitionEnv.digest_value]
 change ok (NMX_R2_InverseBytes.fromKey (env.sha256 (p.val.map NMX_R2_Carrier.bytes))) = _
 rw [parts,key]
#print axioms key
#print axioms parts
#print axioms descriptor
end NMX_R8_Digest241
end
