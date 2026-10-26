import RPz7_Hir_ScheduleSource
import RPz7_Hir_CallLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ScheduleLog
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def reads (H : Bytes → State) (store : Store) : Schedule A B → List (Bytes × State)
  | .done _ => []
  | .inspect k => reads H store (k store)
  | .ask query k => (query,H query) :: reads H store (k (H query))
  | .invoke call k =>
    let head := Hir_Call.native native1 native2 copy allocator id store call
    SdkC_Source.readLog (Hir_CallLog.attempts c hashv copy allocator id store call) ++
      reads H head.1 (k head.2.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)
    reads H head.1 (k head.2)
  | .rollback k => reads H store k

theorem exact_reads
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (store : Store) (schedule : Schedule A B) :
    (eval H (Hir_Schedule.program native1 copy allocator id c hashv store schedule)).1 =
      reads c hashv native1 native2 copy allocator id H store schedule := by
  induction schedule generalizing store with
  | done value => rfl
  | inspect k ih => exact ih store store
  | ask query k ih =>
    simp only [Hir_Schedule.program,eval,reads,ih]
  | invoke call k ih =>
    simp only [Hir_Schedule.program,eval_bind,eval,List.append_nil]
    rw [Hir_CallSource.effect c hashv copy allocator id native1 native2 extraction sha256 H p1 syscall]
    rw [Hir_CallLog.exact_log c hashv copy allocator id sha256 H p1 syscall,ih]
    rfl
  | foreign caller key value k ih =>
    simp only [Hir_Schedule.program,eval_bind,eval,List.append_nil]
    rw [ih]
    rfl
  | rollback k ih =>
    simp only [Hir_Schedule.program,eval_bind,eval,List.append_nil]
    rw [ih]
    rfl

#print axioms exact_reads
end AspisR1.Hir_ScheduleLog
end
