import Hir_LifetimeLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_WriterCharge
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A)) (site : CallAt A)
    (member : site ∈ calls native1 native2 copy allocator id H initial schedule)

include extraction p1 syscall member

theorem reached_reads :
    ∃ front back,
      (eval H (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)).1 =
        front ++ SdkC_Source.readLog (Hir_CallLog.attempts c hashv copy allocator id site.before site.call) ++ back := by
  obtain ⟨front,back,reads⟩ := Hir_BirthReads.source_reads c hashv native1 native2 copy allocator id H initial schedule site member
  refine ⟨front,back ++ SdkC_Source.readLog (SdkC_Source.run hashv (secondCode c hashv allocator id
    (run native1 native2 copy allocator id H initial schedule).1 (run native1 native2 copy allocator id H initial schedule).2.2) []).2,?_⟩
  rw [Hir_LifetimeLog.exact_reads c hashv native1 native2 extraction copy allocator id sha256 H p1 syscall,reads]
  simp only [List.append_assoc]

theorem charged (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1) :
    (SdkC_Source.readLog (Hir_CallLog.attempts c hashv copy allocator id site.before site.call)).length ≤ Q0+Q1 := by
  obtain ⟨front,back,reads⟩ := Hir_BirthReads.source_reads c hashv native1 native2 copy allocator id H initial schedule site member
  have actual := Hir_ScheduleLog.exact_reads c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall initial schedule
  have bound := scheduledBound H
  rw [actual,reads,List.length_append,List.length_append] at bound
  omega

#print axioms reached_reads
#print axioms charged
end AspisR1.Hir_WriterCharge
end
