import RPz7_CPP_RunErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_ProgramErasure
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle CPP_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

/-- Literal program equality, preserving every reached oracle read, native
failure, reply and branch. Malformed-count calls add no oracle query. -/
theorem exact {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (schedule : CPP_Schedule.Schedule A B) :
    CPP_Schedule.program n1 copy allocator id c hashv store schedule =
      Hir_Schedule.program n1 copy allocator id c hashv store (erase schedule) := by
  induction schedule generalizing store with
  | done value => rfl
  | inspect k ih => exact ih store store
  | ask query k ih =>
    simp only [CPP_Schedule.program,erase,Hir_Schedule.program]
    congr 1
    funext answer
    exact ih answer store
  | foreign caller key value k ih => simp only [CPP_Schedule.program,erase,Hir_Schedule.program,ih]
  | rollback k ih => simp only [CPP_Schedule.program,erase,Hir_Schedule.program,ih]
  | invoke input k ih =>
    by_cases good : compatible input
    · simp only [CPP_Schedule.program,erase,Hir_Schedule.program,
        CPP_Oracle.program,if_pos good,ih]
    · simp only [CPP_Schedule.program,erase,Hir_Schedule.program,
        CPP_Oracle.program,if_neg good,AspisV8R19.OracleProgramOps.bind,ih]

#print axioms exact
end AspisR1.CPP_ProgramErasure
end
