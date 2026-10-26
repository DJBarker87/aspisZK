import RPz7_DrvC_CutAcceptance
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_PublicCarrier
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames

theorem public_length {F C : Type} (c : Configuration F C)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s) :
    f.pub.val.length = 1880 := by
  have decoded : AspisS6CurrentCodecInstallation.decode f.pub = ok (.Ok f.statement) := cuts.decode
  obtain ⟨encoded,returned,contents⟩ := AspisS6CurrentCodecInstallation.accepted_inverse f.pub f.statement decoded
  rw [← contents]
  exact encoded.property

theorem fits (pub : Slice U8) (length : pub.val.length = 1880) :
    75 + (bytesOf pub.val).length ≤ SelectedTranscriptParams.L := by
  simp only [bytesOf,List.length_map,length]
  norm_num [SelectedTranscriptParams.L]

def input (pub proof : Slice U8) (fits : 75 + (bytesOf pub.val).length ≤ SelectedTranscriptParams.L) :
    OraclePortStoredExperimentC4.Input :=
  ⟨⟨bytesOf pub.val,fits,0⟩,Port1_StoredCarrier.proof (bytesOf proof.val),bytesOf proof.val⟩

theorem public_bytes (pub proof : Slice U8) (fit : 75 + (bytesOf pub.val).length ≤ SelectedTranscriptParams.L) :
    (input pub proof fit).statement.pubBytes = bytesOf pub.val := rfl

theorem stored_bytes (pub proof : Slice U8) (fit : 75 + (bytesOf pub.val).length ≤ SelectedTranscriptParams.L) :
    (input pub proof fit).stored = bytesOf proof.val := rfl

#print axioms public_length
#print axioms fits
#print axioms public_bytes
#print axioms stored_bytes
end AspisR1.DrvC_PublicCarrier
end
