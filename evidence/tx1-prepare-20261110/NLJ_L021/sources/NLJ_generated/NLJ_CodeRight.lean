import NLJ_ObservedDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_CodeRight
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
theorem right {A : Type} (c : Code A) : PreparedHashCode.bind c Code.done = c := by
 induction c with
 | done a => rfl
 | step r k ih => simp only [PreparedHashCode.bind]; congr; funext a; exact ih a
 | digest D h p k ih => simp only [PreparedHashCode.bind]; congr; funext a; exact ih a
theorem same {A B : Type} (c : Code A) (f g : A → Code B) (h : ∀ a, f a = g a) :
 PreparedHashCode.bind c f = PreparedHashCode.bind c g := congrArg (PreparedHashCode.bind c) (funext h)
#print axioms right
#print axioms same
end AspisR1.NLJ_CodeRight
end
