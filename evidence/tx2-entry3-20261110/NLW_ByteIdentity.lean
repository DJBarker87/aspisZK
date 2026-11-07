import NLW_CommittedRoots
import NLM_ScalarLaws
set_option autoImplicit false
noncomputable section
namespace NLW_ByteIdentity
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.SqueezeOracleBridge
/-- Exact byte carriers, no hash or address equality is used. -/
theorem byte_injective (a b : U8) (same : decodeByte a=decodeByte b) : a=b := by
 apply NLM_ScalarLaws.scalar_eq
 exact congrArg (fun x : AspisV8R19.DuplexFrames.Byte=>x.val) same

theorem bytes_injective (a b : List U8)
 (same : MultiproofConeCanonical.bytesOf a=MultiproofConeCanonical.bytesOf b) : a=b := by
 induction a generalizing b with
 | nil => cases b <;> simp_all [MultiproofConeCanonical.bytesOf]
 | cons x xs ih =>
   cases b with
   | nil => simp [MultiproofConeCanonical.bytesOf] at same
   | cons y ys =>
     have parts:=List.cons.inj same
     have head:=byte_injective x y parts.1
     have tail:=ih ys parts.2
     rw [head,tail]
/-- Both roots survive actual persisted checkpoint bytes and the SAME proof
byte identity. Neither identity is inferred from a pointer or digest alone. -/
theorem both_transport (oldCheckpoint checkpoint oldProof proof : Slice U8)
 (saved : NLW_CommittedRoots.Both oldCheckpoint oldProof)
 (cp : MultiproofConeCanonical.bytesOf checkpoint.val=
       MultiproofConeCanonical.bytesOf oldCheckpoint.val)
 (pr : MultiproofConeCanonical.bytesOf proof.val=
       MultiproofConeCanonical.bytesOf oldProof.val) :
 NLW_CommittedRoots.Both checkpoint proof := by
 have hc:=bytes_injective _ _ cp
 have hp:=bytes_injective _ _ pr
 simpa only [NLW_CommittedRoots.Both,NLW_CommittedRoots.Root1,
  NLW_CommittedRoots.proofRoot,NLW_Root0.Binds,hc,hp] using saved
#print byte_injective
#print bytes_injective
#print both_transport
#print axioms byte_injective
#print axioms bytes_injective
#print axioms both_transport
end NLW_ByteIdentity
