import Hir_ReaderEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_SelectedOrigin
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem causal_writer {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (initial : Store) (schedule : Schedule A (Hir_Choice.Submission A))
    (genesis : ∀ key, (initial key).owner = id → ¬ Initialized (initial key).data)
    (allowed : admissible native1 native2 copy allocator id H initial schedule)
    (post : Heap (Nat → Record)) (final : A)
    (accepted : let out := run native1 native2 copy allocator id H initial schedule
      let chosen := out.2.2
      second native2 allocator (load out.1 chosen.layout) id chosen.data chosen.slot chosen.state = ok (.Ok (post,final))) :
    let out := run native1 native2 copy allocator id H initial schedule
    ∃ site ∈ calls native1 native2 copy allocator id H initial schedule,
      Birth native1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data site := by
  let out := run native1 native2 copy allocator id H initial schedule
  let chosen := out.2.2
  have native := (second_accepted native2 allocator (load out.1 chosen.layout) id chosen.data chosen.slot chosen.state
    final post accepted).1
  have source := (extraction.stage2 id _ chosen.data chosen.slot).symm.trans native
  have owner := Hir_ReaderEntry.owner c law out.1 chosen.layout id chosen.data chosen.slot source
  have marker := Hir_ReaderEntry.marker c out.1 chosen.layout id chosen.data chosen.slot source
  exact Hir_GenesisOrigin.selected_writer native1 native2 copy allocator id H initial schedule _ genesis allowed owner marker

#print axioms causal_writer
end AspisR1.Hir_SelectedOrigin
end
