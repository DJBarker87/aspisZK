import CPP_AtomicRecordNative
import CPP_AtomicRecordErasure
import Hir_LifetimeExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicLifetime
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- All transaction queries, including aborted parents, precede the selected
TX2's exact source wrapper. Provenance uses only committed recorded sites. -/
def program (initial : Store) (schedule : Schedule A (Call A)) :
    Program Bytes State (Hir_LifetimeExperiment.Execution A) :=
  AspisV8R19.OracleProgramOps.bind (CPP_AtomicRecorded.program c hashv n1 copy allocator id initial schedule) fun recorded =>
    AspisV8R19.OracleProgramOps.bind (Hir_PartialOracle.program hashv
      (secondCode c hashv allocator id recorded.1.1 recorded.1.2.2)) fun reply =>
        .done (recorded,reply)

theorem result (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A)) :
    (eval H (program c hashv n1 copy allocator id initial schedule)).2 =
      let out := CPP_AtomicSchedule.run n1 n2 copy allocator id H initial schedule
      ((out,CPP_AtomicSchedule.sites n1 n2 copy allocator id H initial schedule),
        second n2 allocator (load out.1 out.2.2.layout) id out.2.2.data out.2.2.slot out.2.2.state) := by
  simp only [program,eval_bind,eval]
  rw [CPP_AtomicRecordNative.result c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall,
    Hir_CallSource.second_result c hashv allocator id n1 n2 extraction sha256 H p1 syscall]

#print axioms result
end AspisR1.CPP_AtomicLifetime
end
