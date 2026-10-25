import Hir_LifetimeBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_SelectedExecution
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem selected {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A))
    (genesis : ∀ key, (initial key).owner = id → ¬ Initialized (initial key).data)
    (allowed : admissible native1 native2 copy allocator id H initial schedule)
    (post2 : Heap (Nat → Record)) (final2 : A)
    (accepted2 : let out := run native1 native2 copy allocator id H initial schedule
      second native2 allocator (load out.1 out.2.2.layout) id out.2.2.data out.2.2.slot out.2.2.state = ok (.Ok (post2,final2))) :
    let out := run native1 native2 copy allocator id H initial schedule
    ∃ writer,
      search native1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data (calls native1 native2 copy allocator id H initial schedule) = some writer ∧
      pairOf native1 copy allocator id
        (eval H (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)).2 =
        some (Hir_FirstChoice.input writer.site.before writer.site.call,.ok (.Ok (writer.saved,writer.post,writer.final)),
          some (Hir_Choice.input out.1 out.2.2,.ok (.Ok (post2,final2)))) ∧
      writer.site ∈ calls native1 native2 copy allocator id H initial schedule ∧
      Birth native1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data writer.site ∧
      first native1 copy allocator (load writer.site.before writer.site.call.layout) id writer.site.call.data writer.site.call.state =
        ok (.Ok (writer.saved,writer.post,writer.final)) := by
  let out := run native1 native2 copy allocator id H initial schedule
  have birth := Hir_SelectedOrigin.causal_writer c law native1 native2 hashv extraction copy allocator id H initial schedule
    genesis allowed post2 final2 accepted2
  obtain ⟨writer,found⟩ := Hir_Search.complete native1 copy allocator id _ _ _ birth
  obtain ⟨member,writerBirth,accepted1,equal⟩ := Hir_Search.sound native1 copy allocator id _ _ _ writer found
  refine ⟨writer,found,?_,member,writerBirth,accepted1⟩
  rw [Hir_LifetimeNative.result c hashv native1 native2 extraction copy allocator id sha256 H p1 syscall]
  simp only [pairOf,found,accepted2]

#print axioms selected
end AspisR1.Hir_SelectedExecution
end
