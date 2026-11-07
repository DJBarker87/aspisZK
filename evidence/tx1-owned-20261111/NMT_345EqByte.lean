import Aeneas
set_option autoImplicit false
noncomputable section
namespace NMT_345Std
open Aeneas Aeneas.Std Result
/-- Exact short-circuit library comparison on a generic element comparison.
A stopped comparison propagates before any later element is inspected. -/
def listEq {A B : Type} (same : A → B → Result Bool) : List A → List B → Result Bool
 | [],[] => .ok true
 | [],_::_ => .ok false
 | _::_,[] => .ok false
 | x::xs,y::ys => do
   let b ← same x y
   if b then listEq same xs ys else .ok false

def eqByte (x y : U8) : Result Bool := .ok (decide (x = y))

/-- An explicit function-argument equation, rather than whole-list reduction. -/
theorem eqByte_form : eqByte = (fun (x y : U8) => .ok (decide (x = y))) := rfl
#print axioms eqByte_form
end NMT_345Std
