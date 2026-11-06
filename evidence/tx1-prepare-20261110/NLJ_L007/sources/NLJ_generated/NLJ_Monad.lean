import NLJ_ObservedStep
import RPz7_AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Monad
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem bind_pure {A B : Type} (a : A) (k : A → Code B) : PreparedHashCode.bind (.done a) k = k a := rfl
theorem bind_assoc {A B C : Type} (c : Code A) (f : A → Code B) (g : B → Code C) :
 PreparedHashCode.bind (PreparedHashCode.bind c f) g = PreparedHashCode.bind c (fun a => PreparedHashCode.bind (f a) g) := by
 induction c with
 | done a => rfl
 | step r k ih => simp only [PreparedHashCode.bind]; congr; funext a; exact ih a
 | digest D h p k ih => simp only [PreparedHashCode.bind]; congr; funext a; exact ih a
#print axioms bind_pure
#print axioms bind_assoc
end AspisR1.NLJ_Monad
end
