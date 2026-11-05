import NIL_ResultCases
set_option autoImplicit false
namespace NIL_SpineCongr
open Aeneas Aeneas.Std Result

theorem prod {A B C : Type} (x : A × B) (f g : A → B → C)
 (h : ∀ a b,f a b=g a b) : (let (a,b):=x;f a b)=(let (a,b):=x;g a b) := by
 cases x with | mk a b => exact h a b
#print axioms prod
end NIL_SpineCongr
