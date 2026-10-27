import R1Z.PDict_FormatterDictionaryMap
set_option autoImplicit false
namespace R1Z.PDict_ResultTransport
open Aeneas Aeneas.Std PDict_FormatterDictionaryMap
variable {A B C : Type}

theorem map_bind (f : B → C) (r : Result A) (g : A → Result B) :
    resultMap f (do let a ← r; g a) = (do let a ← r; resultMap f (g a)) := by
  cases r <;> rfl

theorem bind_map (f : A → B) (r : Result A) (g : B → Result C) :
    (do let b ← resultMap f r; g b) = (do let a ← r; g (f a)) := by
  cases r <;> rfl

theorem map_comp (f : A → B) (g : B → C) (r : Result A) :
    resultMap g (resultMap f r) = resultMap (g ∘ f) r := by
  cases r <;> rfl

theorem map_id (r : Result A) : resultMap id r = r := by cases r <;> rfl

theorem map_ok (f : A → B) (a : A) : resultMap f (.ok a) = .ok (f a) := rfl

theorem map_fail (f : A → B) (e : Aeneas.Std.Error) : resultMap f (.fail e) = .fail e := rfl

theorem map_div (f : A → B) : resultMap f .div = .div := rfl

#print axioms map_bind
#print axioms bind_map
#print axioms map_comp
#print axioms map_id
#print axioms map_ok
#print axioms map_fail
#print axioms map_div
end R1Z.PDict_ResultTransport
