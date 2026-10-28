import Aeneas
set_option autoImplicit false
namespace NBP_BindPair
open Aeneas Aeneas.Std Result
/-- Move the bind through the generated pair destructuring without unfolding
any operation or buffer. -/
theorem pair {A B C D : Type} (x : A × B) (f : A → B → Result C) (k : C → Result D) :
    ((let (a,b):=x; f a b) >>= k) = (let(a,b):=x; f a b >>= k) := by
  cases x
  rfl
theorem cases_bind {A B C D : Type} (x : A × B) (f : A → B → Result C) (k : C → Result D) :
    (Prod.casesOn x f >>= k) = Prod.casesOn x (fun a b => f a b >>= k) := by
  cases x
  rfl
#print axioms cases_bind
#print axioms pair
end NBP_BindPair
