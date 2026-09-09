import PartialFoldRecovery

/-! Keep eligibility/filter elaboration symbolic before specializing the
selected QM31/domain instances. No concrete field enumeration. -/
set_option autoImplicit false
namespace AspisV8.PreAnchorEligibility
open AspisV8.PartialFoldRecovery
variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [Algebra F K]
variable {n m : Nat}

theorem eligible_subset (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (ix iy : Fin m → F) (received : Fin (4*m) → K) (B : Nat) (A : Finset K) :
    closeFoldChallenges encoder ix iy received B A⊆A := by
  classical
  exact Finset.filter_subset _ _

theorem eligible_mem (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (ix iy : Fin m → F) (received : Fin (4*m) → K) (B : Nat) (A : Finset K)
    (a : K) (ha : a∈A) (final : Fin n → K)
    (close : (foldedBad encoder ix iy received a final).card≤B) :
    a∈closeFoldChallenges encoder ix iy received B A := by
  classical
  exact Finset.mem_filter.mpr ⟨ha, final, close⟩

#print axioms eligible_subset
#print axioms eligible_mem
end AspisV8.PreAnchorEligibility
