import RPz7_CPP_AtomicSource
import RPz7_CPP_Protection
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicTrace
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_Atomic
attribute [local instance] Classical.propDecidable
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem classified {A B : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State) (before : Store)
    (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply B)) :
    Trace ops id before (CPP_Atomic.run n1 n2 copy allocator id H before code).2.1
      (CPP_Atomic.run n1 n2 copy allocator id H before code).1 := by
  by_cases success : committed (CPP_Schedule.run n1 n2 copy allocator id H before code).2.2
  · rw [CPP_Atomic.run,CPP_AtomicLaws.commit before _ success,CPP_RunErasure.exact]
    exact Hir_ScheduleTrace.classified ops law n1 n2 source copy std allocator id H before (CPP_Schedule.erase code)
  · rw [CPP_Atomic.run,CPP_AtomicLaws.rollback before _ success]
    exact Trace.cons (Step.rollback before) (Trace.nil before)

#print axioms classified
end AspisR1.CPP_AtomicTrace
end
