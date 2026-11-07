import LIBC_HashPartitions
import NJS_BatchLeaf
set_option autoImplicit false
noncomputable section
namespace LIBC_CohortHash
open Aeneas Aeneas.Std
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
abbrev CBytes := AspisV8R19.DuplexFrames.Bytes
def host (b : CBytes) : RSL.Bytes := b.map (fun x => UInt8.ofNat x.val)
def H (env : RSL.Env) (b : CBytes) : State :=
 decodeState (LIB_Env.nativeKey (env.sha256 (LIBC_HashPartitions.split (host b))))
theorem scalar (b : U8) : UInt8.ofNat (decodeByte b).val = NNC_ByteCarriers.hostByte b := by
 apply UInt8.toNat_inj.mp
 change b.val % 256 = b.val
 exact Nat.mod_eq_of_lt b.hmax
theorem flat (parts : Slice (Slice U8)) : host (flatten parts) = (NNC_ResumeEvents.parts parts).flatten := by
 simp only [host,flatten,NNC_ResumeEvents.parts,NNC_ByteCarriers.host,List.map_map,
  List.map_flatMap,List.flatten_map,Function.comp_def,scalar]
theorem output (env : RSL.Env) (parts : Slice (Slice U8))
 (shape : LIBC_HashPartitions.Shape (NNC_ResumeEvents.parts parts)) :
 encodeState (H env (flatten parts)) = LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts parts)) := by
 unfold H
 rw [flat,LIBC_HashPartitions.exact _ shape,array_roundtrip]
theorem backend (env : RSL.Env) (parts : Slice (Slice U8))
 (shape : LIBC_HashPartitions.Shape (NNC_ResumeEvents.parts parts)) :
 (NJS_RuntimeDigest.backend (H env)).digest () parts = LIB_Env.hashv env parts := by
 change .ok (encodeState (H env (flatten parts))) = _
 rw [output env parts shape]
 rfl
#print axioms scalar
#print axioms flat
#print axioms output
#print axioms backend
end LIBC_CohortHash
