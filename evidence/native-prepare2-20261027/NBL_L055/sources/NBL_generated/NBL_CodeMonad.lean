import S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1.NBL_CodeMonad
open AspisR1PublicPreparation.PreparedHashCode

theorem associative {A B C : Type} (p : Code A) (f : A → Code B) (g : B → Code C) :
    ((p >>= f) >>= g)=(p >>= fun a => f a >>= g) := by
  change AspisR1PublicPreparation.PreparedHashCode.bind
    (AspisR1PublicPreparation.PreparedHashCode.bind p f) g=
    AspisR1PublicPreparation.PreparedHashCode.bind p (fun a => AspisR1PublicPreparation.PreparedHashCode.bind (f a) g)
  induction p with
  | done a => rfl
  | step r c ih =>
    apply congrArg (Code.step r)
    funext a
    exact ih a
  | digest D hash parts c ih =>
    apply congrArg (Code.digest D hash parts)
    funext a
    exact ih a

theorem bind_same {A B : Type} (p : Code A) (f g : A → Code B) (same : ∀ a,f a=g a) :
    (p >>= f)=(p >>= g) := congrArg (fun k => p >>= k) (funext same)

theorem pure_bind {A B : Type} (a : A) (f : A → Code B) :
    ((pure a : Code A) >>= f)=f a := rfl

#print axioms associative
#print axioms bind_same
#print axioms pure_bind
end AspisR1.NBL_CodeMonad
