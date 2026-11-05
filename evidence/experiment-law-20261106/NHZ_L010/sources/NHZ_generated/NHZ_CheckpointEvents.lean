import NHZ_ScalarEvents
import NHS_CheckpointPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHZ_DRIVER
open Aeneas Aeneas.Std Result CheckpointBytes5Effect CheckpointBytes5Writer
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)

section
variable (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Prepared) (a : Accumulator) (domain : NGC_KNE_Caller.WriterDomain p a)
    (proof publicBytes : Slice U8)
local notation "code" => NGC_KNE_Writer.sourceProgram p a domain proof publicBytes
local notation "body" hp hu => NGC_KNE_Writer.materialize p a domain hp hu

/-- SAME checkpoint bytes and three ordered digest occurrences. The writer's
116 byte transitions remain its existing caller-domain packet. -/
theorem checkpoint_success (hp hu hc : Digest)
    (proofEdge : hashv (singletonParts proof) = .ok hp)
    (publicEdge : hashv (singletonParts publicBytes) = .ok hu)
    (checksumEdge : hashv (checksumParts (body hp hu)) = .ok hc) :
    Cuts hashv code (.ok (NGC_KNE_Writer.returned p a domain hp hu hc))
      [⟨singletonParts proof,.ok hp⟩,⟨singletonParts publicBytes,.ok hu⟩,
       ⟨checksumParts (body hp hu),.ok hc⟩] := by
  rw [NGC_KNE_Writer.program_eq,NGC_KNE_Writer.returned_eq]
  rw [NGC_KNE_Writer.materialize_eq] at checksumEdge ⊢
  apply Cuts.leaf
  apply NGQ_Cuts.Trace.readOk _ _ hp proofEdge
  apply NGQ_Cuts.Trace.readOk _ _ hu publicEdge
  apply NGQ_Cuts.Trace.readOk _ _ hc checksumEdge
  exact .done _

theorem checkpoint_proof_fail (error : Error)
    (edge : hashv (singletonParts proof) = .fail error) :
    Cuts hashv code (.fail error) [⟨singletonParts proof,.fail error⟩] :=
  .leaf (.readFail _ _ error edge)

theorem checkpoint_proof_div
    (edge : hashv (singletonParts proof) = .div) :
    Cuts hashv code .div [⟨singletonParts proof,.div⟩] :=
  .leaf (.readDiv _ _ edge)

theorem checkpoint_public_fail (hp : Digest) (error : Error)
    (proofEdge : hashv (singletonParts proof) = .ok hp)
    (edge : hashv (singletonParts publicBytes) = .fail error) :
    Cuts hashv code (.fail error)
      [⟨singletonParts proof,.ok hp⟩,⟨singletonParts publicBytes,.fail error⟩] :=
  .leaf (.readOk _ _ hp proofEdge _ _ (.readFail _ _ error edge))

theorem checkpoint_public_div (hp : Digest)
    (proofEdge : hashv (singletonParts proof) = .ok hp)
    (edge : hashv (singletonParts publicBytes) = .div) :
    Cuts hashv code .div
      [⟨singletonParts proof,.ok hp⟩,⟨singletonParts publicBytes,.div⟩] :=
  .leaf (.readOk _ _ hp proofEdge _ _ (.readDiv _ _ edge))

theorem checkpoint_checksum_fail (hp hu : Digest) (error : Error)
    (proofEdge : hashv (singletonParts proof) = .ok hp)
    (publicEdge : hashv (singletonParts publicBytes) = .ok hu)
    (edge : hashv (checksumParts (body hp hu)) = .fail error) :
    Cuts hashv code (.fail error)
      [⟨singletonParts proof,.ok hp⟩,⟨singletonParts publicBytes,.ok hu⟩,
       ⟨checksumParts (body hp hu),.fail error⟩] :=
  .leaf (.readOk _ _ hp proofEdge _ _ (.readOk _ _ hu publicEdge _ _ (.readFail _ _ error edge)))

theorem checkpoint_checksum_div (hp hu : Digest)
    (proofEdge : hashv (singletonParts proof) = .ok hp)
    (publicEdge : hashv (singletonParts publicBytes) = .ok hu)
    (edge : hashv (checksumParts (body hp hu)) = .div) :
    Cuts hashv code .div
      [⟨singletonParts proof,.ok hp⟩,⟨singletonParts publicBytes,.ok hu⟩,
       ⟨checksumParts (body hp hu),.div⟩] :=
  .leaf (.readOk _ _ hp proofEdge _ _ (.readOk _ _ hu publicEdge _ _ (.readDiv _ _ edge)))

#print axioms checkpoint_success
#print axioms checkpoint_proof_fail
#print axioms checkpoint_proof_div
#print axioms checkpoint_public_fail
#print axioms checkpoint_public_div
#print axioms checkpoint_checksum_fail
#print axioms checkpoint_checksum_div
end
end AspisR1.NHZ_DRIVER
