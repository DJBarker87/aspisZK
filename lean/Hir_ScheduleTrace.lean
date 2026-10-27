import Hir_Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ScheduleTrace
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers GExq_AccountExperiment Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A B : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data,
      AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = native1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program)

include law source trustedCopy

theorem classified (H : Bytes → State) (store : Store) (schedule : Schedule A B) :
    Trace ops id store (run native1 native2 copy allocator id H store schedule).2.1
      (run native1 native2 copy allocator id H store schedule).1 := by
  induction schedule generalizing store with
  | done value => exact Trace.nil store
  | inspect k ih => exact ih store store
  | ask query k ih => exact ih (H query) store
  | invoke call k ih =>
    exact Trace.cons (Hir_CallClassify.classified ops law native1 native2 source copy trustedCopy allocator id store call)
      (ih (Hir_Call.native native1 native2 copy allocator id store call).2.2
        (Hir_Call.native native1 native2 copy allocator id store call).1)
  | foreign caller key value k ih =>
    exact Trace.cons
      (Hiq_NativeClassify.step ops law native1 source copy trustedCopy allocator id store (.foreign caller key value))
      (ih (Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)).2
        (Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)).1)
  | rollback k ih => exact Trace.cons (Step.rollback store) (ih store)

theorem protection (H : Bytes → State) (store : Store) (schedule : Schedule A B) (key : Nat)
    (owner : (store key).owner = id) (marker : Initialized (store key).data) :
    (∀ event ∈ (run native1 native2 copy allocator id H store schedule).2.1, S2X.Preserves key event) ∧
      (run native1 native2 copy allocator id H store schedule).1 key = store key :=
  Hist_TraceProtection.trace_frame ops id store _ key _
    (classified ops law native1 native2 source copy trustedCopy allocator id H store schedule) owner marker

#print axioms classified
#print axioms protection
end AspisR1.Hir_ScheduleTrace
end
