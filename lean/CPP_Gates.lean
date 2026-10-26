import CPP_Invocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Gates
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation
attribute [local instance] Classical.propDecidable
variable {A : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (input : Invocation A)

theorem first_rejected (bad : ¬ Hiq_ReleaseRoute.stage1 input.call.data ∨ input.count ≠ 3) :
    CPP_Invocation.first n1 copy allocator id store input = ok (.Err .InvalidInstructionData) := by
  unfold CPP_Invocation.first
  rw [if_neg (by tauto)]

theorem second_rejected (bad : ¬ Hiq_ReleaseRoute.asq8 input.call.data ∨ input.count ≠ 7) :
    CPP_Invocation.second n2 allocator id store input = ok (.Err .InvalidInstructionData) := by
  unfold CPP_Invocation.second
  rw [if_neg (by tauto)]

theorem first_accepted (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (accepted : CPP_Invocation.first n1 copy allocator id store input = ok (.Ok (saved,post,final))) :
    Hiq_ReleaseRoute.stage1 input.call.data ∧ input.count = 3 ∧
      S2W_D189Wrappers.first n1 copy allocator (load store input.call.layout) id input.call.data input.call.state =
        ok (.Ok (saved,post,final)) := by
  unfold CPP_Invocation.first at accepted
  split at accepted
  · rename_i good
    exact ⟨good.1,good.2,accepted⟩
  · cases accepted

theorem second_accepted (post : Heap (Nat → Record)) (final : A)
    (accepted : CPP_Invocation.second n2 allocator id store input = ok (.Ok (post,final))) :
    Hiq_ReleaseRoute.asq8 input.call.data ∧ input.count = 7 ∧
      S2W_D189Wrappers.second n2 allocator (load store input.call.layout) id input.call.data input.call.slot input.call.state =
        ok (.Ok (post,final)) := by
  unfold CPP_Invocation.second at accepted
  split at accepted
  · rename_i good
    exact ⟨good.1,good.2,accepted⟩
  · cases accepted

#print axioms first_rejected
#print axioms second_rejected
#print axioms first_accepted
#print axioms second_accepted
end AspisR1.CPP_Gates
end
