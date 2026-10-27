import RPz7_S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result

theorem code_bind_assoc {A B C : Type} (p : Code A) (f : A → Code B) (g : B → Code C) :
    ((p >>= f) >>= g)=(p >>= fun a => f a >>= g) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    change Code.step r (fun a => bind (bind (next a) f) g)=
      Code.step r (fun a => bind (next a) (fun b => bind (f b) g))
    congr 1
    funext a
    exact ih a
  | digest D hash parts next ih =>
    change Code.digest D hash parts (fun a => bind (bind (next a) f) g)=
      Code.digest D hash parts (fun a => bind (next a) (fun b => bind (f b) g))
    congr 1
    funext a
    exact ih a

theorem code_left_unit {A B : Type} (a : A) (k : A → Code B) :
    ((pure a : Code A) >>= k)=k a := rfl

#print axioms code_bind_assoc
#print axioms code_left_unit
end AspisR1PublicPreparation.PreparedHashCode
