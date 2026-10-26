import CPP_AtomicSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicRunTrace
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem classified {A B : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State) (before : Store)
    (schedule : Schedule A B) :
    Trace ops id before (run n1 n2 copy allocator id H before schedule).2.1
      (run n1 n2 copy allocator id H before schedule).1 := by
  induction schedule generalizing before with
  | done value => exact Trace.nil before
  | inspect k ih => exact ih before before
  | ask query k ih => exact ih (H query) before
  | transaction code k ih =>
    exact CPP_TraceAppend.append ops id
      (CPP_AtomicTrace.classified ops law n1 n2 source copy std allocator id H before code)
      (ih (CPP_Atomic.run n1 n2 copy allocator id H before code).2.2
        (CPP_Atomic.run n1 n2 copy allocator id H before code).1)

#print axioms classified
end AspisR1.CPP_AtomicRunTrace
end
