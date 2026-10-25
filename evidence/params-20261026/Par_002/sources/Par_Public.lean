import DrvC_PublicCarrier
import Par_Parameters
set_option autoImplicit false
noncomputable section
namespace AspisR1.Par_Public
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open DrvC_Installation S2W_NativeConsolidation

/-- No initFits argument: derive it from the accepted installed decoder's size. -/
def input (pub proof : Slice U8) (length : pub.val.length = 1880) :
    OraclePortStoredExperimentC4.Input :=
  ⟨⟨bytesOf pub.val, DrvC_PublicCarrier.fits pub length, 2⟩,
    Port1_StoredCarrier.proof (bytesOf proof.val), bytesOf proof.val⟩

theorem input_bytes (pub proof : Slice U8) (length : pub.val.length = 1880) :
    (input pub proof length).statement.pubBytes = bytesOf pub.val ∧
    (input pub proof length).stored = bytesOf proof.val ∧
    (input pub proof length).statement.tag = 2 := ⟨rfl,rfl,rfl⟩

/-- The length fact is an output of these SAME source cuts, not a new premise. -/
theorem accepted_public_bound {F C : Type} (c : Configuration F C)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s) :
    (bytesOf f.pub.val).length = 1880 ∧
    75 + (bytesOf f.pub.val).length ≤ SelectedTranscriptParams.L := by
  have size := DrvC_PublicCarrier.public_length c accounts1 accounts2 saved f s cuts
  exact ⟨by simpa only [bytesOf, List.length_map] using size,
    DrvC_PublicCarrier.fits f.pub size⟩

#print axioms input_bytes
#print axioms accepted_public_bound
end AspisR1.Par_Public
end
