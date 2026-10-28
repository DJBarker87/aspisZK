import RPz7_ExtractedDigest32Begin
set_option autoImplicit false
namespace AspisR1.JFm_Result
open Aeneas Aeneas.Std Result

theorem pair_ok {α β γ : Type} (a : α) (b : β) (k : α → β → Result γ) :
    (do let (x,y) ← ok (a,b); k x y)=k a b := rfl

#print axioms pair_ok
end AspisR1.JFm_Result
