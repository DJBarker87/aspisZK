import CPP_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Compatibility
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle
attribute [local instance] Classical.propDecidable
variable {A : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (input : Invocation A)

theorem valid (good : compatible input) :
    CPP_Invocation.native n1 n2 copy allocator id store input =
      Hir_Call.native n1 n2 copy allocator id store input.call := by
  cases route : Hiq_ReleaseRoute.route input.call.data with
  | first => exact CPP_Classify.first_valid n1 n2 copy allocator id store input route (by simpa only [compatible,route] using good)
  | second => exact CPP_Classify.second_valid n1 n2 copy allocator id store input route (by simpa only [compatible,route] using good)
  | reject => simp only [CPP_Invocation.native,Hir_Call.native,route]

theorem invalid (bad : ¬ compatible input) :
    CPP_Invocation.native n1 n2 copy allocator id store input =
      (store,.rollback,rejectedReply input) := by
  cases route : Hiq_ReleaseRoute.route input.call.data with
  | first =>
    rw [CPP_Classify.first_invalid n1 n2 copy allocator id store input route (by simpa only [compatible,route] using bad)]
    simp only [rejectedReply,route]
  | second =>
    rw [CPP_Classify.second_invalid n1 n2 copy allocator id store input route (by simpa only [compatible,route] using bad)]
    simp only [rejectedReply,route]
  | reject => exact False.elim (bad (by simp only [compatible,route]))

#print axioms valid
#print axioms invalid
end AspisR1.CPP_Compatibility
end
