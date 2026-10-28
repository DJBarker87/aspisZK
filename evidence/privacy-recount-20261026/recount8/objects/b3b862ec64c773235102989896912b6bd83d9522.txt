import PV_B3P_HelperList224
namespace PV_B3P_HelperConstant224
open Aeneas Aeneas.Std PV_B3P_RustResult
set_option autoImplicit false

theorem map_constant {α β : Type} (xs : List α) (f : α → β) (value : β)
    (h : ∀ x ∈ xs, f x = value) : xs.map f = List.replicate xs.length value := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons,List.length_cons,List.replicate_succ]
    rw [h head (by simp),ih (fun x hx => h x (by simp [hx]))]

theorem collect_constant {F E : Type} (value : F) (n : Nat) :
    collect (List.replicate n (Result.ok (core.result.Result.Ok value) : Result (core.result.Result F E))) =
      .ok (.Ok (List.replicate n value)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,collect,bindR,ih]

#print axioms map_constant
#print axioms collect_constant
end PV_B3P_HelperConstant224
