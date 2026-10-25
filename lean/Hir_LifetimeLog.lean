import Hir_BirthReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_LifetimeLog
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem exact_reads {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A)) :
    (eval H (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)).1 =
      let out := run native1 native2 copy allocator id H initial schedule
      Hir_ScheduleLog.reads c hashv native1 native2 copy allocator id H initial schedule ++
        SdkC_Source.readLog (SdkC_Source.run hashv (secondCode c hashv allocator id out.1 out.2.2) []).2 := by
  simp only [Hir_LifetimeExperiment.program,eval_bind,eval,List.append_nil]
  rw [Hir_RecordNative.result c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall]
  have logs := congrArg Prod.fst (Hir_RecordErasure.exact c hashv native1 copy allocator id H initial schedule)
  rw [← logs,Hir_ScheduleLog.exact_reads c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall]
  congr 1
  exact (Hir_PartialOracle.exact hashv sha256 H p1 syscall _ []).2.symm

#print axioms exact_reads
end AspisR1.Hir_LifetimeLog
end
