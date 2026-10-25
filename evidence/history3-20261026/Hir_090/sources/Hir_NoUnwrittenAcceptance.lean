import Hir_SelectedClean
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_NoUnwrittenAcceptance
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Source-derived rejection of a genesis account fabricated only by foreign
zero-data owner assignment/rollback. This does not assume checkpoint retention
or any hash injectivity, and it needs no successful native TX1 premise. -/
theorem rejects {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (initial : Store) (schedule : Schedule A (Call A))
    (genesis : ∀ key, (initial key).owner = id → ¬ Initialized (initial key).data)
    (allowed : admissible native1 native2 copy allocator id H initial schedule)
    (noCalls : calls native1 native2 copy allocator id H initial schedule = [])
    (post2 : Heap (Nat → Record)) (final2 : A) :
    let out := run native1 native2 copy allocator id H initial schedule
    second native2 allocator (load out.1 out.2.2.layout) id out.2.2.data out.2.2.slot out.2.2.state ≠ ok (.Ok (post2,final2)) := by
  intro accepted
  obtain ⟨site,member,birth⟩ := Hir_SelectedOrigin.causal_writer c law native1 native2 hashv extraction copy allocator id H
    initial schedule genesis allowed post2 final2 accepted
  rw [noCalls] at member
  cases member

#print axioms rejects
end AspisR1.Hir_NoUnwrittenAcceptance
end
