import CPP_Selected
import Hir_SelectedExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Origin
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel Hir_WriterSelect
open CPP_Invocation CPP_Oracle CPP_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The final guarded native TX2 selects its actual causal TX1 writer. Neither
an independently accepted TX1, a matching checkpoint key nor found is input. -/
theorem selected {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : CPP_Schedule.Schedule A (Call A)) (count2 : Nat)
    (genesis : ∀ key, (initial key).owner = id → ¬ Initialized (initial key).data)
    (allowed : admissible n1 n2 copy allocator id H initial (erase schedule))
    (post2 : Heap (Nat → Record)) (final2 : A)
    (accepted2 : let out := CPP_Schedule.run n1 n2 copy allocator id H initial schedule
      CPP_Invocation.second n2 allocator id out.1 ⟨out.2.2,count2⟩ = ok (.Ok (post2,final2))) :
    let out := CPP_Schedule.run n1 n2 copy allocator id H initial schedule
    count2 = 7 ∧ ∃ writer,
      search n1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data
        (calls n1 n2 copy allocator id H initial (erase schedule)) = some writer ∧
      writer.site ∈ calls n1 n2 copy allocator id H initial (erase schedule) ∧
      Birth n1 copy allocator id (out.2.2.layout.handles 6).1 (out.1 (out.2.2.layout.handles 6).1).data writer.site ∧
      S2W_D189Wrappers.first n1 copy allocator (load writer.site.before writer.site.call.layout) id
        writer.site.call.data writer.site.call.state = ok (.Ok (writer.saved,writer.post,writer.final)) ∧
      S2W_D189Wrappers.second n2 allocator (load out.1 out.2.2.layout) id out.2.2.data out.2.2.slot out.2.2.state =
        ok (.Ok (post2,final2)) := by
  let out := CPP_Schedule.run n1 n2 copy allocator id H initial schedule
  have ⟨magic,count,native2⟩ := CPP_Gates.second_accepted n2 allocator id out.1 ⟨out.2.2,count2⟩ post2 final2 accepted2
  have ordinary2 := native2
  dsimp only [out] at ordinary2
  rw [CPP_RunErasure.exact] at ordinary2
  obtain ⟨writer,found,pair,member,birth,native1⟩ := Hir_SelectedExecution.selected c law n1 n2 hashv extraction
    copy allocator id sha256 H p1 syscall initial (erase schedule) genesis allowed post2 final2 ordinary2
  refine ⟨count,writer,?_,member,?_,native1,native2⟩
  · simpa only [out,CPP_RunErasure.exact] using found
  · simpa only [out,CPP_RunErasure.exact] using birth

#print axioms selected
end AspisR1.CPP_Origin
end
