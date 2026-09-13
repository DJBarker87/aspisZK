import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel

/-! Generic algebra for a witness-free public-coset sampler. This file does
not assert the missing V8 public-quotient source theorem. -/
set_option autoImplicit false

namespace AspisV8Privacy

section

variable {F R O Q : Type*} [Field F]
variable [AddCommGroup R] [Module F R] [AddCommGroup O] [Module F O]
variable [AddCommGroup Q] [Module F Q]

theorem same_public_coset_has_correction (M : R →ₗ[F] O)
    (L : O →ₗ[F] Q) (kernelExact : LinearMap.ker L = LinearMap.range M)
    (offset representative : O) (samePublic : L offset = L representative) :
    ∃ d, M d = offset - representative := by
  have hzero : L (offset - representative) = 0 := by
    rw [map_sub, samePublic, sub_self]
  have hmem : offset - representative ∈ LinearMap.ker L := hzero
  rw [kernelExact] at hmem
  exact LinearMap.mem_range.mp hmem

theorem public_representative_transport (M : R →ₗ[F] O)
    (offset representative : O) (d : R) (correction : M d = offset - representative)
    (r : R) : representative + M (r + d) = offset + M r := by
  rw [map_add, correction]
  abel

def translatePublicCosetCoins (d : R) : R ≃ R where
  toFun r := r + d
  invFun r := r - d
  left_inv r := by simp
  right_inv r := by simp

#print axioms same_public_coset_has_correction
#print axioms public_representative_transport
#print axioms translatePublicCosetCoins

end

end AspisV8Privacy
