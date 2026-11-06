import NLC_BridgeGoal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Monad
open Aeneas Aeneas.Std AspisR1PublicPreparation
open PreparedHashCode
 theorem bind_assoc {A B C : Type} (x : Code A) (f : A → Code B) (g : B → Code C) :
 bind (bind x f) g = bind x (fun a => bind (f a) g) := by
 induction x with
 | done a => rfl
 | step r k ih => simp only [bind]; congr; funext b; exact ih b
 | digest D h p k ih => simp only [bind]; congr; funext b; exact ih b
 theorem bind_done {A B : Type} (a : A) (f : A → Code B) : bind (.done a) f = f a := rfl
#print axioms bind_assoc
#print axioms bind_done
end AspisR1.NLI_Monad
end
