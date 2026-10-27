import CPP_RunErasure
import CPP_Write
import Hir_ScheduleTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Protection
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle CPP_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Count-complete arbitrary finite native schedules inherit source/runtime
protection, including malformed calls, failed prefixes, adversary reads and
foreign owner-authorized writes. No no-write premise is supplied. -/
theorem protection {A B : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State) (store : Store)
    (schedule : CPP_Schedule.Schedule A B) (key : Nat)
    (owner : (store key).owner = id) (marker : Initialized (store key).data) :
    (∀ event ∈ (CPP_Schedule.run n1 n2 copy allocator id H store schedule).2.1, S2X.Preserves key event) ∧
      (CPP_Schedule.run n1 n2 copy allocator id H store schedule).1 key = store key := by
  rw [CPP_RunErasure.exact]
  exact Hir_ScheduleTrace.protection ops law n1 n2 source copy std allocator id H store (erase schedule) key owner marker

#print axioms protection
end AspisR1.CPP_Protection
end
