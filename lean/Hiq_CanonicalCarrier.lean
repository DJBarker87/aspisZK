import DrvC_PublicCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_CanonicalCarrier
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames
open OraclePortStoredExperimentC4

def submission (pub proof : Slice U8) : Port1_StoredCarrier.Submission :=
  ⟨bytesOf pub.val,bytesOf proof.val⟩
def input (pub proof : Slice U8) : Input := Port1_StoredCarrier.input (submission pub proof)

theorem public_bytes (pub proof : Slice U8)
    (fit : 75 + (bytesOf pub.val).length ≤ SelectedTranscriptParams.L) :
    (input pub proof).statement.pubBytes = bytesOf pub.val :=
  Port1_StoredCarrier.public_bytes _ fit

theorem stored_bytes (pub proof : Slice U8) : (input pub proof).stored = bytesOf proof.val := rfl

theorem carried (pub proof : Slice U8) : Port1_StoredCarrier.Carried (input pub proof) :=
  Port1_StoredCarrier.input_carried _

theorem proof (pub proof : Slice U8) : (input pub proof).proof = Port1_StoredCarrier.proof (bytesOf proof.val) := rfl

theorem physical {F C : Type} (c : DrvC_Installation.Configuration F C) (pub proof : Slice U8)
    (fit : 75 + (bytesOf pub.val).length ≤ SelectedTranscriptParams.L) :
    DrvC_Implementation.driver c (input pub proof) =
      DrvC_Implementation.driver c (DrvC_PublicCarrier.input pub proof fit) :=
  DrvC_Implementation.physical c _ _ (public_bytes pub proof fit) rfl

#print axioms public_bytes
#print axioms stored_bytes
#print axioms carried
#print axioms proof
#print axioms physical
end AspisR1.Hiq_CanonicalCarrier
end
