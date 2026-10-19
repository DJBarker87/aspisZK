import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Rat.Defs

set_option autoImplicit false
namespace M31EquivUniformTransport

universe u v w

def fiber {X : Type u} {Y : Type v} (f : X → Y) (y : Y) :=
  {x : X // f x = y}

theorem fiber_equiv_symm {X : Type u} {A : Type v} {B : Type w}
    (e : A ≃ B) (f : X → A) (b : B) :
    fiber (fun x => e (f x)) b ≃ fiber f (e.symm b) where
  toFun x := ⟨x.1, by
    have h := congrArg e.symm x.2
    simpa using h⟩
  invFun x := ⟨x.1, by
    have h := congrArg e x.2
    simpa using h⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem fiber_card_equiv_symm {X : Type u} {A : Type v} {B : Type w}
    (e : A ≃ B) (f : X → A) (b : B) :
    Nat.card (fiber (fun x => e (f x)) b) = Nat.card (fiber f (e.symm b)) :=
  Nat.card_congr (fiber_equiv_symm e f b)

theorem uniform_mass_equiv_symm {A : Type u} {B : Type v}
    (e : A ≃ B) (mass : A → ℚ) (c : ℚ)
    (h : ∀ a, mass a = c) : ∀ b, mass (e.symm b) = c := by
  intro b
  exact h (e.symm b)

#print axioms fiber_equiv_symm
#print axioms fiber_card_equiv_symm
#print axioms uniform_mass_equiv_symm

end M31EquivUniformTransport
