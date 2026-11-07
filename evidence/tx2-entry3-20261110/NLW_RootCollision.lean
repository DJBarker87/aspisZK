import NLW_AuthenticatedRoots
set_option autoImplicit false
noncomputable section
namespace NLW_RootCollision
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical
/-- Exact existing collision event on full proof bytes; no no-collision or
 digest-injectivity premise is inserted into the hash realization row. -/
def Collision (H : Bytes → State) (oldProof proof : Slice U8) : Prop :=
 bytesOf oldProof.val≠bytesOf proof.val ∧ H (bytesOf oldProof.val)=H (bytesOf proof.val)
/-- Combine concrete SAME-header equality with OLD provenance. If the new
 caller roots do not bind, the two full input buffers witness a collision. -/
theorem alternatives (H : Bytes → State) (saved loaded proof1 pub1 proof2 pub2 : Slice U8)
 (persisted : bytesOf loaded.val=bytesOf saved.val)
 (oldRoots : NLW_CommittedRoots.Both saved proof1)
 (writer : NLW_ReaderHeader.decode (bytesOf saved.val)=some (H (bytesOf proof1.val),H (bytesOf pub1.val)))
 (reader : NLW_ReaderHeader.decode (bytesOf loaded.val)=some (H (bytesOf proof2.val),H (bytesOf pub2.val))) :
 NLW_CommittedRoots.Both loaded proof2 ∨ Collision H proof1 proof2 := by
 have checked:=NLW_AuthenticatedRoots.digest_matches H saved loaded proof1 pub1 proof2 pub2
  persisted writer reader
 have oldLoaded:=NLW_ByteIdentity.both_transport saved loaded proof1 proof1 oldRoots persisted rfl
 by_cases same : bytesOf proof2.val=bytesOf proof1.val
 · exact .inl (NLW_ByteIdentity.both_transport loaded loaded proof1 proof2 oldLoaded rfl same)
 · exact .inr ⟨Ne.symm same,checked.1.symm⟩
#print Collision
#print alternatives
#print axioms alternatives
end NLW_RootCollision
