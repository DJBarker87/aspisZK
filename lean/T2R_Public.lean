import Par_Headline
import Par_Transcript
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_Public
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open S2W_NativeConsolidation MultiproofConeCanonical

/-- The public carrier is constructed from the original cuts' bytes. -/
def Facts (pub proof : Slice U8) : Prop :=
  ∃ i : OraclePortStoredExperimentC4.Input,
    i.statement.pubBytes = bytesOf pub.val ∧ i.stored = bytesOf proof.val ∧
    i.statement.tag = 2 ∧ i.statement.pubBytes.length = 1880 ∧
    75 + i.statement.pubBytes.length ≤ SelectedTranscriptParams.L ∧
    ∀ tr : RawCutTranscriptRun.ErasedPrefix,
      tr.statement.pubBytes = bytesOf pub.val →
      75 + tr.statement.pubBytes.length ≤ SelectedTranscriptParams.L

theorem on_cuts {F C : Type} (c : DrvC_Installation.Configuration F C)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) accounts1 accounts2 saved f s) :
    Facts f.pub f.proof := by
  have size := DrvC_PublicCarrier.public_length c accounts1 accounts2 saved f s cuts
  obtain ⟨length,fit⟩ := Par_Public.accepted_public_bound c accounts1 accounts2 saved f s cuts
  refine ⟨Par_Public.input f.pub f.proof size,rfl,rfl,rfl,length,fit,?_⟩
  intro tr same
  exact (Par_Transcript.accepted_initFits c accounts1 accounts2 saved f s cuts tr same).2

#print axioms on_cuts
end AspisR1.T2R_Public
end
