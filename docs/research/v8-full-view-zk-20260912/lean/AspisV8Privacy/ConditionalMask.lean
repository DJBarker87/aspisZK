import AspisV8Privacy.AffineMask
import Mathlib.Algebra.Group.Prod

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM.
The NEW view must be hidden after fixing ALL old disclosures. This is why
rank(B) is insufficient; source certificates must solve A*d=0 and B*d=shift.
-/
set_option autoImplicit false
namespace AspisV8Privacy
noncomputable section
variable {R U V T : Type*}
variable [AddCommGroup R] [AddCommGroup U] [AddCommGroup V] [AddCommGroup T]

def jointObservation (A : R →+ U) (B : R →+ V) : R →+ (U × V) where
  toFun r := (A r, B r)
  map_zero' := by simp
  map_add' r s := by simp

def kernelCorrection (K : T →+ R) (J : V →+ T) (shift : V) : R := K (J shift)

theorem kernel_correction_preserves_old (A : R →+ U) (K : T →+ R)
    (J : V →+ T) (inKernel : ∀ t, A (K t) = 0) (shift : V) (r : R) :
    A (r + kernelCorrection K J shift) = A r := by
  simp [kernelCorrection, map_add, inKernel]

theorem kernel_correction_changes_new (B : R →+ V) (K : T →+ R)
    (J : V →+ T) (rightInverse : ∀ v, B (K (J v)) = v) (shift : V) (r : R) :
    B (r + kernelCorrection K J shift) = B r + shift := by
  simp [kernelCorrection, map_add, rightInverse]

/-- Concrete simultaneous transport, with old witness offsets permitted.
No independence of the two observation blocks is assumed. -/
theorem joint_affine_same_law [Fintype R]
    (A : R →+ U) (B : R →+ V) (a₀ a₁ : U) (b₀ b₁ : V) (d : R)
    (oldSolved : A d = a₀ - a₁) (newSolved : B d = b₀ - b₁) :
    SameUniformLaw
      (affineView (jointObservation A B) (a₀,b₀))
      (affineView (jointObservation A B) (a₁,b₁)) := by
  apply affine_same_uniform_law _ _ _ d
  exact Prod.ext oldSolved newSolved

/-- Parametrize a conditioned affine fiber by the ACTUAL kernel, not by
unconditioned random coins. A source-derived kernel basis is still needed. -/
def kernelToFiber (A : R →+ U) (r₀ : R) :
    {r : R // A r = 0} ≃ {r : R // A r = A r₀} where
  toFun r := ⟨r₀ + r.val, by simp [map_add, r.property]⟩
  invFun r := ⟨r.val - r₀, by simp [map_sub, r.property]⟩
  left_inv r := by apply Subtype.ext; dsimp; abel
  right_inv r := by apply Subtype.ext; dsimp; abel

#print axioms kernel_correction_preserves_old
#print axioms kernel_correction_changes_new
#print axioms joint_affine_same_law
#print axioms kernelToFiber
end
end AspisV8Privacy
