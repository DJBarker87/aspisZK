import RPz7_Hir_FactoryLoad
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_FactoryCharge
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (initial : Store)
    (scheduler : Hir_Factory.Scheduler A)

theorem reads
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (input : GExq_AccountExperiment.FirstInputs A) (saved : alloc.vec.Vec U8)
    (post : Heap (Nat → Record)) (final : A) :
    (eval H (Hir_Factory.choose c hashv native1 copy allocator id initial scheduler input saved post final)).1 =
      Hir_ScheduleLog.reads c hashv native1 native2 copy allocator id H
        (commit initial (input.entry.handles 2).1 saved) (scheduler input saved post final) :=
  Hir_ChoiceLog.exact c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall _ _

#print axioms reads
end AspisR1.Hir_FactoryCharge
end
