import PV_L1_Logged
set_option autoImplicit false
namespace PV_L1_Projection
/-- Project an emitted restoration tuple symbolically instead of expanding
its array data or duplicating all of the following error branches. -/
theorem prod_case {A B C : Type} (p : A × B) (f : A → B → C) :
    (match p with | (a,b) => f a b) = f p.1 p.2 := by
  cases p; rfl
#print axioms prod_case
end PV_L1_Projection
