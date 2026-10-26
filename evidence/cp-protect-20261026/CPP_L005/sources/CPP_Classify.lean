import CPP_Gates
import Hir_CallClassify
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Classify
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation
attribute [local instance] Classical.propDecidable
variable {A : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (input : Invocation A)

theorem first_valid (route : Hiq_ReleaseRoute.route input.call.data = .first) (count : input.count = 3) :
    CPP_Invocation.native n1 n2 copy allocator id store input =
      Hir_Call.native n1 n2 copy allocator id store input.call := by
  have stage := (Hiq_ReleaseRoute.first_iff _).mp route
  simp only [CPP_Invocation.native,Hir_Call.native,route,CPP_Invocation.first,if_pos ⟨stage,count⟩]

theorem first_invalid (route : Hiq_ReleaseRoute.route input.call.data = .first) (count : input.count ≠ 3) :
    CPP_Invocation.native n1 n2 copy allocator id store input =
      (store,.rollback,.inl (.ok (.Err .InvalidInstructionData))) := by
  simp only [CPP_Invocation.native,route,CPP_Gates.first_rejected n1 copy allocator id store input (Or.inr count),firstEffect]

theorem second_valid (route : Hiq_ReleaseRoute.route input.call.data = .second) (count : input.count = 7) :
    CPP_Invocation.native n1 n2 copy allocator id store input =
      Hir_Call.native n1 n2 copy allocator id store input.call := by
  have stage := ((Hiq_ReleaseRoute.second_iff _).mp route).2
  simp only [CPP_Invocation.native,Hir_Call.native,route,CPP_Invocation.second,if_pos ⟨stage,count⟩]

theorem second_invalid (route : Hiq_ReleaseRoute.route input.call.data = .second) (count : input.count ≠ 7) :
    CPP_Invocation.native n1 n2 copy allocator id store input =
      (store,.rollback,.inr (.ok (.Err .InvalidInstructionData))) := by
  simp only [CPP_Invocation.native,route,CPP_Gates.second_rejected n2 allocator id store input (Or.inr count)]

theorem rejected (route : Hiq_ReleaseRoute.route input.call.data = .reject) :
    CPP_Invocation.native n1 n2 copy allocator id store input =
      (store,.rollback,.inr (.ok (.Err .InvalidInstructionData))) := by
  simp only [CPP_Invocation.native,route]

theorem classified (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (std : S2W_TrustedStd.TrustedStd copy) :
    Step ops id store (CPP_Invocation.native n1 n2 copy allocator id store input).2.1
      (CPP_Invocation.native n1 n2 copy allocator id store input).1 := by
  cases route : Hiq_ReleaseRoute.route input.call.data with
  | reject => rw [rejected n1 n2 copy allocator id store input route]; exact Step.rollback store
  | first =>
    by_cases count : input.count = 3
    · rw [first_valid n1 n2 copy allocator id store input route count]
      exact Hir_CallClassify.classified ops law n1 n2 source copy std allocator id store input.call
    · rw [first_invalid n1 n2 copy allocator id store input route count]; exact Step.rollback store
  | second =>
    by_cases count : input.count = 7
    · rw [second_valid n1 n2 copy allocator id store input route count]
      exact Hir_CallClassify.classified ops law n1 n2 source copy std allocator id store input.call
    · rw [second_invalid n1 n2 copy allocator id store input route count]; exact Step.rollback store

#print axioms first_valid
#print axioms first_invalid
#print axioms second_valid
#print axioms second_invalid
#print axioms rejected
#print axioms classified
end AspisR1.CPP_Classify
end
