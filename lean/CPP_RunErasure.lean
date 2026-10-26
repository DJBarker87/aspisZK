import CPP_Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_RunErasure
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle CPP_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

theorem exact {A B : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (store : Store) (schedule : CPP_Schedule.Schedule A B) :
    CPP_Schedule.run n1 n2 copy allocator id H store schedule =
      Hir_Schedule.run n1 n2 copy allocator id H store (erase schedule) := by
  induction schedule generalizing store with
  | done value => rfl
  | inspect k ih => exact ih store store
  | ask query k ih => exact ih (H query) store
  | foreign caller key value k ih => simp only [CPP_Schedule.run,erase,Hir_Schedule.run,ih]
  | rollback k ih => simp only [CPP_Schedule.run,erase,Hir_Schedule.run,ih]
  | invoke input k ih =>
    by_cases good : compatible input
    · simp only [CPP_Schedule.run,erase,if_pos good,Hir_Schedule.run,
        CPP_Compatibility.valid n1 n2 copy allocator id store input good,ih]
    · simp only [CPP_Schedule.run,erase,if_neg good,Hir_Schedule.run,
        CPP_Compatibility.invalid n1 n2 copy allocator id store input good,ih]

#print axioms exact
end AspisR1.CPP_RunErasure
end
