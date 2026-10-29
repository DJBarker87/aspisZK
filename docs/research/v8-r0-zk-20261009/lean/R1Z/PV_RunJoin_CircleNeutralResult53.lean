import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralResult53
/-- Equality of full Results plus an invariant on every successful output. -/
def Aligned {A : Type} (P : A → Prop) (x y : Result A) : Prop :=
  x = y ∧ ∀ a, x = ok a → P a

theorem returned {A : Type} (P : A → Prop) (x y : Result A) (a : A)
    (hx : x=ok a) (hy : y=ok a) (ha : P a) : Aligned P x y := by
  refine ⟨hx.trans hy.symm,?_⟩
  intro b hb
  have he : a=b := by exact Result.ok.inj (hx.symm.trans hb)
  simpa only [← he] using ha

theorem bind {A B : Type} {P : A → Prop} {Q : B → Prop}
    {x y : Result A} {f g : A → Result B} (h : Aligned P x y)
    (hk : ∀ a, P a → Aligned Q (f a) (g a)) :
    Aligned Q (do let a ← x; f a) (do let a ← y; g a) := by
  rcases h with ⟨he,hp⟩
  subst y
  cases hx : x with
  | fail e => exact ⟨rfl,by intro b hb; cases hb⟩
  | div => exact ⟨rfl,by intro b hb; cases hb⟩
  | ok a => exact hk a (hp a hx)

theorem failed {A : Type} (P : A → Prop) (e : Error) : Aligned P (.fail e) (.fail e) :=
  ⟨rfl,by intro a h; cases h⟩

theorem diverged {A : Type} (P : A → Prop) : Aligned P (.div) (.div) :=
  ⟨rfl,by intro a h; cases h⟩

#print axioms Aligned
#print axioms returned
#print axioms bind
#print axioms failed
#print axioms diverged
end R1Z.PV_RunJoin_CircleNeutralResult53
