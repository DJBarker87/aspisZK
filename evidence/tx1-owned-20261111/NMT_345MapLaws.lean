import NMT_345Carriers
set_option autoImplicit false
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One symbolic Boolean guard; no concrete account or buffer is reduced. -/
theorem mapOuter_if {A B : Type} (f : A → B) (bad : Bool) (x y : Result A) :
 mapOuter f (if bad then x else y) = if bad then mapOuter f x else mapOuter f y := by
 cases bad <;> rfl

theorem mapCore_if {A B E F : Type} (f : A → B) (g : E → F) (bad : Bool)
 (x y : core.result.Result A E) :
 mapCore f g (if bad then x else y) = if bad then mapCore f g x else mapCore f g y := by
 cases bad <;> rfl

theorem mapOuter_ok {A B : Type} (f : A → B) (x : A) :
 mapOuter f (.ok x) = .ok (f x) := rfl

theorem mapCore_inverse {A E : Type} (r : core.result.Result A PE) :
 mapCore id fromPE (mapCore id toPE r) = r := by
 cases r <;> simp only [mapCore,from_toPE,id_eq]
#print axioms mapOuter_if
#print axioms mapCore_if
#print axioms mapOuter_ok
#print axioms mapCore_inverse
end NMT_345
