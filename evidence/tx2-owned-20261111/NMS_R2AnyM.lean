import NFY_Part060
set_option autoImplicit false
namespace NMS_R2AnyM
open Aeneas Aeneas.Std Result
/-- Symbolic short-circuit std loop totality. No concrete buffer is unrolled. -/
theorem total {A : Type} (predicate : A → Result Bool)
 (returns : ∀ a, ∃ b, predicate a = ok b) (xs : List A) :
 ∃ b, List.anyM predicate xs = ok b := by
 induction xs with
 | nil => exact ⟨false,rfl⟩
 | cons x xs ih =>
   obtain ⟨b,first⟩ := returns x
   cases b with
   | false =>
     obtain ⟨last,rest⟩ := ih
     refine ⟨last,?_⟩
     simpa only [List.anyM_cons,first,bind_tc_ok,Bool.false_eq_true,↓reduceIte] using rest
   | true =>
     refine ⟨true,?_⟩
     simp only [List.anyM_cons,first,bind_tc_ok,↓reduceIte]
     rfl
#print axioms total
end NMS_R2AnyM
