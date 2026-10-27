import RPz7_Hir_Recorded
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_RecordErasure
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem exact {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (store : Store) (schedule : Schedule A B) :
    eval H (Hir_Schedule.program native1 copy allocator id c hashv store schedule) =
      ((eval H (Hir_Recorded.program c hashv native1 copy allocator id store schedule)).1,
       (eval H (Hir_Recorded.program c hashv native1 copy allocator id store schedule)).2.1) := by
  induction schedule generalizing store with
  | done value => rfl
  | inspect k ih => exact ih store store
  | ask query k ih =>
    simp only [Hir_Schedule.program,Hir_Recorded.program,eval]
    rw [ih]
  | invoke call k ih =>
    simp only [Hir_Schedule.program,Hir_Recorded.program,eval_bind,eval]
    rw [ih]
  | foreign caller key value k ih =>
    simp only [Hir_Schedule.program,Hir_Recorded.program,eval_bind,eval]
    rw [ih]
  | rollback k ih =>
    simp only [Hir_Schedule.program,Hir_Recorded.program,eval_bind,eval]
    rw [ih]

#print axioms exact
end AspisR1.Hir_RecordErasure
end
