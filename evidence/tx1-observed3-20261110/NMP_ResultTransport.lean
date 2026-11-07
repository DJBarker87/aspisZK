import NMP_Transport_T13
import NMP_DirectBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ResultTransport
open Aeneas Aeneas.Std Result
/-- Every outer abort/diverge and every Rust error payload is retained. -/
def outer {A B : Type} (f : A → B) : Result A → Result B
 | .ok a => .ok (f a) | .fail e => .fail e | .div => .div

def inner {A B E F : Type} (f : A → B) (g : E → F) : core.result.Result A E → core.result.Result B F
 | .Ok a => .Ok (f a) | .Err e => .Err (g e)

theorem outer_inverse {A B : Type} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (r : Result A) : outer g (outer f r)=r := by
 cases r <;> simp only [outer,inverse]

theorem inner_inverse {A B E F : Type} (f : A → B) (g : B → A)
 (ef : E → F) (eg : F → E) (inverse : ∀ x,g (f x)=x) (errors : ∀ e,eg (ef e)=e)
 (r : core.result.Result A E) : inner g eg (inner f ef r)=r := by
 cases r <;> simp only [inner,inverse,errors]

theorem outer_bind {A B C : Type} (f : B → C) (r : Result A) (k : A → Result B) :
 outer f (Aeneas.Std.bind r k) = Aeneas.Std.bind r (fun a => outer f (k a)) := by
 cases r <;> rfl

theorem stopped {A B : Type} (f : A → B) (e : Error) :
 outer f (.fail e) = .fail e ∧ outer f (.div : Result A) = .div := ⟨rfl,rfl⟩
#print axioms outer_inverse
#print axioms inner_inverse
#print axioms outer_bind
#print axioms stopped
end AspisR1.NMP_ResultTransport
