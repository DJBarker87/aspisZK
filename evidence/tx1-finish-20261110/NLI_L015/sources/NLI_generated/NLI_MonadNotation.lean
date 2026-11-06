import NLI_RunLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Notation
open Aeneas Aeneas.Std AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem assoc {A B C : Type} (p : Code A) (f : A → Code B) (g : B → Code C) :
 ((p >>= f) >>= g) = (p >>= fun a => f a >>= g) := NLI_Monad.bind_assoc p f g
theorem pure_left {A B : Type} (a : A) (f : A → Code B) :
 ((pure a : Code A) >>= f) = f a := rfl
theorem lift_ok {A B : Type} (a : A) (f : A → Code B) :
 run ((liftM (Result.ok a) : Code A) >>= f) = run (f a) := rfl
theorem congr_bind {A B : Type} (p : Code A) (k l : A → Code B)
 (eqs : ∀ a, run (k a) = run (l a)) : run (p >>= k) = run (p >>= l) :=
 NLI_RunLaws.bind_congr p k l eqs
#print axioms assoc
#print axioms pure_left
#print axioms lift_ok
#print axioms congr_bind
end AspisR1.NLI_Notation
end
