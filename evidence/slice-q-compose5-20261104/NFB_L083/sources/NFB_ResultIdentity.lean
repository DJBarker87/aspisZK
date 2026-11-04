import NFB_BindPair
set_option autoImplicit false
namespace NFB_ResultIdentity
open Aeneas Aeneas.Std Result

theorem right {A : Type} (r : Result A) : (do let x←r;ok x)=r := by cases r <;> rfl

theorem pair_bind {A B C : Type} (r : Result (A×B)) (f : A → B → Result C) :
 (do let (a,b)←r;f a b)=(do let p←r;f p.1 p.2) := by
 cases r with
 | fail => rfl
 | div => rfl
 | ok p => cases p;rfl
#print axioms right
#print axioms pair_bind
end NFB_ResultIdentity
