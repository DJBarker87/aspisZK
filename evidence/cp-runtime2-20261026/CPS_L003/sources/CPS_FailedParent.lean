import CPP_AtomicRecordNative
import CPP_Compatibility
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_FailedParent
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation
open AspisV8R19.DuplexFrames

def code {A : Type} (input : Invocation A) : CPP_Schedule.Schedule A (CPP_Atomic.Reply Unit) :=
  .invoke input (fun _ => .done (.ok (.Err .InvalidInstructionData)))

variable {A : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (before : Store) (input : Invocation A)

/-- An actual reached invocation may be followed by a parent error. This
retains the invocation effect before final atomic settlement. -/
theorem tentative :
    CPP_Schedule.run n1 n2 copy allocator id H before (code input) =
      ((CPP_Invocation.native n1 n2 copy allocator id before input).1,
       [(CPP_Invocation.native n1 n2 copy allocator id before input).2.1],
       .ok (.Err .InvalidInstructionData)) := rfl

theorem rollback :
    CPP_Atomic.run n1 n2 copy allocator id H before (code input) =
      (before,[.rollback],.ok (.Err .InvalidInstructionData)) := rfl

theorem discarded_sites :
    CPP_Atomic.sites n1 n2 copy allocator id H before (code input) = [] := rfl

/-- The accepted native copy really occurs in this tentative source schedule;
it still supplies no committed-parent site after settlement. -/
theorem accepted_copy (route : Hiq_ReleaseRoute.route input.call.data = .first)
    (count : input.count = 3)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (accepted : first n1 copy allocator (load before input.call.layout) id input.call.data input.call.state =
      ok (.Ok (saved,post,final))) :
    CPP_Schedule.run n1 n2 copy allocator id H before (code input) =
      (commit before (input.call.layout.handles 2).1 saved,
       [.committedWrite (input.call.layout.handles 2).1 (MultiproofConeCanonical.bytesOf saved.val)],
       .ok (.Err .InvalidInstructionData)) ∧
    CPP_Atomic.run n1 n2 copy allocator id H before (code input) =
      (before,[.rollback],.ok (.Err .InvalidInstructionData)) ∧
    CPP_Atomic.sites n1 n2 copy allocator id H before (code input) = [] := by
  refine ⟨?_,rollback n1 n2 copy allocator id H before input,
    discarded_sites n1 n2 copy allocator id H before input⟩
  rw [tentative,CPP_Classify.first_valid n1 n2 copy allocator id before input route count]
  simp only [Hir_Call.native,route,accepted,Hir_Call.firstEffect]

#print axioms tentative
#print axioms rollback
#print axioms discarded_sites
#print axioms accepted_copy
end AspisR1.CPS_FailedParent
end
