import AspisV8R16.TransportDual
import AspisV8Baseline.FusedRows

/-! Reuse boundary for the old compact tensor evaluator. The old evaluator
may be composed with this linear map, but must retain the permutation delta,
pivot subtraction, and transported inactive indicator. No nonzero factor,
honest-witness, source-compiler or privacy premise is assumed. -/
set_option autoImplicit false
namespace AspisV8R17.CompactTransport
open scoped BigOperators
variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

def dualLinear (inactive : Finset I) (pivot : I) (order : I ≃ I) :
    (I → K) →ₗ[K] (I → K) where
  toFun := AspisV8R16.transportDual inactive pivot order
  map_add' := by
    intro w v
    funext j
    simp only [AspisV8R16.transportDual, Pi.add_apply]
    split <;> ring
  map_smul' := by
    intro a w
    funext j
    simp only [AspisV8R16.transportDual, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> ring

def indicator (s : Finset I) : I → K := fun j => if j ∈ s then 1 else 0
def pivotMarker (pivot : I) (order : I ≃ I) : I → K :=
  fun j => if order j = pivot then 1 else 0
def otherInactive (inactive : Finset I) (pivot : I) (order : I ≃ I) : I → K :=
  fun j => if order j ∈ inactive.erase pivot then 1 else 0
def permutationDelta (order : I ≃ I) (w : I → K) : I → K :=
  fun j => w (order j) - w j

theorem inactive_to_pivot (inactive : Finset I) (pivot : I)
    (hp : pivot ∈ inactive) (order : I ≃ I) :
    dualLinear (K := K) inactive pivot order (indicator inactive) =
      pivotMarker pivot order := by
  funext j
  by_cases hj : order j = pivot
  · simp [dualLinear, AspisV8R16.transportDual, indicator, pivotMarker, hj, hp]
  · by_cases hi : order j ∈ inactive
    · simp [dualLinear, AspisV8R16.transportDual, indicator, pivotMarker, hj, hi, hp]
    · simp [dualLinear, AspisV8R16.transportDual, indicator, pivotMarker, hj, hi]

theorem dual_split (inactive : Finset I) (pivot : I) (order : I ≃ I)
    (w : I → K) :
    dualLinear inactive pivot order w =
      w + permutationDelta order w - w pivot • otherInactive inactive pivot order := by
  funext j
  simp only [dualLinear, LinearMap.coe_mk, AddHom.coe_mk,
    AspisV8R16.transportDual, permutationDelta, otherInactive,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split <;> simp_all

/-- The old ordinary tensor evaluator, one permutation correction, one fixed
inactive-mask contraction, and one pivot contraction give the exact answer. -/
theorem compact_transport {V : Type*} [AddCommGroup V] [Module K V]
    (L : (I → K) →ₗ[K] V) (inactive : Finset I) (pivot : I)
    (hp : pivot ∈ inactive) (order : I ≃ I) (w : I → K) :
    L (dualLinear inactive pivot order (w + indicator inactive)) =
      L w + L (permutationDelta order w) -
        w pivot • L (otherInactive inactive pivot order) + L (pivotMarker pivot order) := by
  rw [map_add, inactive_to_pivot inactive pivot hp order, dual_split,
    map_add, map_sub, map_add, map_smul]

theorem delta_zero_off_support (order : I ≃ I) (w : I → K) (support : Finset I)
    (hfixed : ∀ j, j ∉ support → order j = j) (j : I) (hj : j ∉ support) :
    permutationDelta order w j = 0 := by
  simp [permutationDelta, hfixed j hj]

/-- Apply the existing fused-row theorem through the repaired transport.
The index-to-Rust-array correspondence is a separate source obligation. -/
theorem fused_rows_through_repair {V : Type*} [AddCommGroup V] [Module K V]
    (L : ((Fin 5 → Fin 4) → K) →ₗ[K] V)
    (inactive : Finset (Fin 5 → Fin 4)) (pivot : Fin 5 → Fin 4)
    (order : (Fin 5 → Fin 4) ≃ (Fin 5 → Fin 4))
    (b : Fin 5 → Fin 4 → K) (k : K) :
    L (dualLinear inactive pivot order
      (AspisV8.FusedRows.tensor (Function.update b 1 (fun d => k*b 1 d + k^3*b 1 d.rev)))) =
    k • L (dualLinear inactive pivot order (AspisV8.FusedRows.tensor b)) +
      k^3 • L (dualLinear inactive pivot order
        (AspisV8.FusedRows.tensor (Function.update b 1 (fun d => b 1 d.rev)))) := by
  exact AspisV8.FusedRows.fuse_through_linear_transport
    (L.comp (dualLinear inactive pivot order)) b k

#print axioms inactive_to_pivot
#print axioms dual_split
#print axioms compact_transport
#print axioms delta_zero_off_support
#print axioms fused_rows_through_repair
end AspisV8R17.CompactTransport
