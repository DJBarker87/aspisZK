import AspisV8Privacy.FiniteGames
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. Fixed affine map only. Pairwise witness
indistinguishability is NOT an efficient public-input zero-knowledge simulator. -/
set_option autoImplicit false
namespace AspisV8Privacy
noncomputable section
variable {R V : Type*} [AddCommGroup R] [AddCommGroup V]

def translateCoins (d : R) : R ≃ R where
  toFun r := r + d
  invFun r := r - d
  left_inv r := by simp
  right_inv r := by simp

def affineView (L : R →+ V) (offset : V) (r : R) : V := offset + L r

theorem affine_shift (L : R →+ V) (b₀ b₁ : V) (d : R)
    (solved : L d = b₀ - b₁) (r : R) :
    affineView L b₁ (r + d) = affineView L b₀ r := by
  simp only [affineView, map_add, solved]
  abel

/-- The exact sufficient criterion is allowed displacement in the mask image;
full output rank is stronger than necessary. The solver must construct d. -/
theorem affine_same_uniform_law [Fintype R]
    (L : R →+ V) (b₀ b₁ : V) (d : R) (solved : L d = b₀ - b₁) :
    SameUniformLaw (affineView L b₀) (affineView L b₁) := by
  apply sameUniformLaw_of_coinEquiv _ _ (translateCoins d)
  intro r
  exact affine_shift L b₀ b₁ d solved r

/-- A dual certificate detects a REAL difference of these affine views.
Whether two V8-valid witnesses realize b₀,b₁ is a SEPARATE obligation. -/
theorem dual_separation {T : Type*} [AddCommGroup T]
    (L : R →+ V) (test : V →+ T) (b₀ b₁ : V)
    (annihilates : ∀ r, test (L r) = 0)
    (different : test b₀ ≠ test b₁) (r₀ r₁ : R) :
    affineView L b₀ r₀ ≠ affineView L b₁ r₁ := by
  intro eq
  have observed := congrArg test eq
  simp only [affineView, map_add, annihilates, add_zero] at observed
  exact different observed

#print axioms affine_shift
#print axioms affine_same_uniform_law
#print axioms dual_separation
end
end AspisV8Privacy
