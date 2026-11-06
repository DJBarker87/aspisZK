import NLJ_ObservedStep
import RPz7_AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Monad
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code bind run)
theorem bind_pure {A B : Type} (a : A) (k : A → Code B) : bind (.done a) k = k a := rfl
theorem bind_assoc {A B C : Type} (c : Code A) (f : A → Code B) (g : B → Code C) :
 bind (bind c f) g = bind c (fun a => bind (f a) g) := by
 induction c with
 | done a => rfl
 | step r k ih => simp only [bind]; congr; funext a; exact ih a
 | digest D h p k ih => simp only [bind]; congr; funext a; exact ih a
#print axioms bind_pure
#print axioms bind_assoc
end AspisR1.NLJ_Monad
end
