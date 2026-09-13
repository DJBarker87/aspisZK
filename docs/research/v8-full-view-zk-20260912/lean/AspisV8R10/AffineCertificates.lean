import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace AspisV8R10
variable {K U V Old T : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup Old] [Module K Old]
variable [AddCommGroup T] [Module K T]

theorem stacked_correction (A : U →ₗ[K] Old) (B : U →ₗ[K] V)
    (da : Old) (db : V) (s u : U) (hsA : A s = da) (hsB : B s = db) :
    (A (u + s), B (u + s)) = (A u + da, B u + db) := by
  simp [map_add, hsA, hsB]

theorem correction_preserves_prefix (A : U →ₗ[K] Old) (B : U →ₗ[K] V)
    (db : V) (s u : U) (hsA : A s = 0) (hsB : B s = db) :
    A (u + s) = A u ∧ B (u + s) = B u + db := by
  simp [map_add, hsA, hsB]

theorem separator_rules_out_correction (B : U →ₗ[K] V) (ell : V →ₗ[K] K)
    (d : V) (zero : ∀ u, ell (B u) = 0) (nonzero : ell d ≠ 0) :
    ¬ ∃ u, B u = d := by
  rintro ⟨u, hu⟩
  exact nonzero (hu ▸ zero u)

theorem ranges_equal_of_two_corrections
    (A : U →ₗ[K] V) (B : T →ₗ[K] V)
    (ab : T →ₗ[K] U) (ba : U →ₗ[K] T)
    (hab : A.comp ab = B) (hba : B.comp ba = A) :
    Set.range A = Set.range B := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨ba u, ?_⟩
    exact LinearMap.congr_fun hba u
  · rintro ⟨t, rfl⟩
    refine ⟨ab t, ?_⟩
    exact LinearMap.congr_fun hab t

theorem affine_fiber_translation (A : U →ₗ[K] V)
    (b d : V) (s u : U) (shift : A s = d - b) (fiber : A u = b) :
    A (u + s) = d := by
  rw [map_add, fiber, shift]
  abel

#print axioms stacked_correction
#print axioms correction_preserves_prefix
#print axioms separator_rules_out_correction
#print axioms ranges_equal_of_two_corrections
#print axioms affine_fiber_translation
end AspisV8R10
