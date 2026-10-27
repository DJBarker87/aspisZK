import CPP_AtomicRecorded
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicRecordErasure
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem exact {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (before : Store) (schedule : Schedule A B) :
    eval H (program n1 copy allocator id c hashv before schedule) =
      ((eval H (CPP_AtomicRecorded.program c hashv n1 copy allocator id before schedule)).1,
       (eval H (CPP_AtomicRecorded.program c hashv n1 copy allocator id before schedule)).2.1) := by
  induction schedule generalizing before with
  | done value => rfl
  | inspect k ih => exact ih before before
  | ask query k ih => simp only [program,CPP_AtomicRecorded.program,eval]; rw [ih]
  | transaction code k ih =>
    simp only [program,CPP_AtomicRecorded.program,eval_bind,eval]
    rw [CPP_AtomicRecord.erasure c hashv n1 copy allocator id before code H,ih]

#print axioms exact
end AspisR1.CPP_AtomicRecordErasure
end
