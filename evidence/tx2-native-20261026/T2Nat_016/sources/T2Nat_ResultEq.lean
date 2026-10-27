import T2Nat_RawJoin
set_option autoImplicit false
namespace AspisR1.T2Nat_ResultEq
open Aeneas Aeneas.Std Result
/-- Equality of every returned value, including returned error values. This
relation deliberately makes no fail-versus-div claim. -/
def EqOk {A : Type} (r s : Result A) : Prop := ∀ a, r = ok a ↔ s = ok a

theorem refl {A : Type} (r : Result A) : EqOk r r := fun _ => Iff.rfl

theorem symm {A : Type} {r s : Result A} (h : EqOk r s) : EqOk s r :=
  fun a => (h a).symm

theorem bind_success {A B : Type} (r : Result A) (k : A → Result B) (b : B) :
    (r >>= k) = ok b ↔ ∃ a, r = ok a ∧ k a = ok b := by
  cases r <;> simp

theorem bind {A B : Type} {r s : Result A} {k l : A → Result B}
    (hr : EqOk r s) (hk : ∀ a, EqOk (k a) (l a)) :
    EqOk (r >>= k) (s >>= l) := by
  intro b
  simp only [bind_success]
  constructor
  · rintro ⟨a,ha,hb⟩; exact ⟨a,(hr a).mp ha,(hk a b).mp hb⟩
  · rintro ⟨a,ha,hb⟩; exact ⟨a,(hr a).mpr ha,(hk a b).mpr hb⟩

#print axioms refl
#print axioms symm
#print axioms bind_success
#print axioms bind
end AspisR1.T2Nat_ResultEq
