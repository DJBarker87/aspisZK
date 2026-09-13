import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs

/-! Pure finite counting, not a random-oracle model. -/
set_option autoImplicit false
namespace AspisV8H1C2
noncomputable section
universe u v w
variable {C : Type u} {D : Type v} {V : Type w}

def fiberCount [Fintype C] (f : C → V) (y : V) : Nat := by
  classical
  exact Fintype.card {c : C // f c = y}

def SameUniformLaw [Fintype C] [Fintype D] (f : C → V) (g : D → V) : Prop :=
  ∀ y, (fiberCount f y : ℚ) / Fintype.card C =
    (fiberCount g y : ℚ) / Fintype.card D

def observationFiberEquiv (f : C → V) (g : D → V) (e : C ≃ D)
    (commutes : ∀ c, g (e c) = f c) (y : V) :
    {c : C // f c = y} ≃ {d : D // g d = y} where
  toFun c := ⟨e c.val, (commutes c.val).trans c.property⟩
  invFun d := ⟨e.symm d.val, by
    rw [← commutes (e.symm d.val), e.apply_symm_apply]
    exact d.property⟩
  left_inv c := by apply Subtype.ext; exact e.symm_apply_apply c.val
  right_inv d := by apply Subtype.ext; exact e.apply_symm_apply d.val

theorem sameUniformLaw_of_equiv [Fintype C] [Fintype D]
    [Nonempty C] [Nonempty D]
    (f : C → V) (g : D → V) (e : C ≃ D)
    (commutes : ∀ c, g (e c) = f c) : SameUniformLaw f g := by
  classical
  intro y
  change (Fintype.card {c : C // f c = y} : ℚ) / (Fintype.card C : ℚ) =
    (Fintype.card {d : D // g d = y} : ℚ) / (Fintype.card D : ℚ)
  rw [Fintype.card_congr (observationFiberEquiv f g e commutes y),
    Fintype.card_congr e]

#print axioms sameUniformLaw_of_equiv
end
end AspisV8H1C2
