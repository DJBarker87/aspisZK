import NLJ_Tx1Fold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Algebra
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
 theorem assoc {A B C : Type} (c : Code A) (f : A → Code B) (g : B → Code C) :
 bind (bind c f) g = bind c (fun a => bind (f a) g) := by
 induction c with
 | done a => rfl
 | step r k ih => simp only [bind]; congr; funext a; exact ih a
 | read p k ih => simp only [bind]; congr; funext a; exact ih a
 theorem right {A : Type} (c : Code A) : bind c Code.done = c := by
 induction c with
 | done a => rfl
 | step r k ih => simp only [bind]; congr; funext a; exact ih a
 | read p k ih => simp only [bind]; congr; funext a; exact ih a
 theorem same {A B : Type} (c : Code A) (f g : A → Code B) (h : ∀ a, f a = g a) :
 bind c f = bind c g := congrArg (bind c) (funext h)
 theorem norm_bind {A B : Type} (c : Code A) (f : A → Code B) :
 NGQ_Normalize.normalize (bind c f) = NGQ_Normalize.normalize (bind (NGQ_Normalize.normalize c) f) := by
 induction c with
 | done a => rfl
 | step r k ih => cases r <;> simp only [bind,NGQ_Normalize.normalize,ih]
 | read p k ih => simp only [bind,NGQ_Normalize.normalize]; congr; funext a; exact ih a
#print axioms assoc
#print axioms right
#print axioms same
#print axioms norm_bind
end AspisR1.NLV_Algebra
end
