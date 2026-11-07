import NND_Carrier
set_option autoImplicit false
namespace NND_Carrier
open Aeneas Aeneas.Std AdapterRw

theorem reply_forth {A B : Type} (f : A → B) (g : B → A) (h : ∀ y, f (g y) = y)
 (x : Except RSL.ProgramError B) : reply f (unreply g x) = x := by
 cases x <;> simp [reply,unreply,h]
#print axioms reply_forth
end NND_Carrier
