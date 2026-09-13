import AspisFormal.V5FriRelationCandidateBridge

/-!
# Algebra at the 256-entry observer boundary

This leaf covers the difficult-to-see representation of the deferred binary
64-by-16 component after the first arity-four fold. It uses the actual source
order [1, alpha^3, alpha^2, alpha] and two halvings. It is not a theorem about
the translated machine integers: the UInt16 bit-mask and canonical-field
representation correspondences remain explicit integration work.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73PrequeryWeights256
open scoped BigOperators
open AspisV5FriRelationCandidateBridge
noncomputable section
variable {K : Type*} [Field K]

/-- Slot order used by the log-eight deferred `weight_at` branch. -/
def deferredPower (alpha : K) (slot : Fin 4) : K :=
  if slot.val = 0 then 1 else
    if slot.val = 1 then alpha ^ 3 else
      if slot.val = 2 then alpha ^ 2 else alpha

def maskIndex (chunk slot : Fin 4) : Fin 16 :=
  ⟨4 * chunk.val + slot.val, by omega⟩

def binaryCovector (mask : Fin 16 → Bool) (j : Fin 16) : K :=
  if mask j then 1 else 0

/-- Mathematical image of the source `slot < 4` loop, before halving. -/
def deferredMaskSum (alpha : K) (mask : Fin 16 → Bool) (chunk : Fin 4) : K :=
  ∑ slot : Fin 4, if mask (maskIndex chunk slot) then deferredPower alpha slot else 0

/-- The source applies `half().half()`, not a single half. -/
def deferredMaskWeight (alpha : K) (mask : Fin 16 → Bool) (chunk : Fin 4) : K :=
  deferredMaskSum alpha mask chunk / 2 / 2

theorem two_halves_eq_quarter (x : K) : x / 2 / 2 = x / 4 := by
  rw [div_div]
  norm_num

/-- Pure finite-field interpretation of the exact deferred source formula. -/
theorem deferredMaskWeight_eq_dualFold
    (alpha : K) (mask : Fin 16 → Bool) (chunk : Fin 4) :
    deferredMaskWeight alpha mask chunk =
      dualWeightFoldValue alpha
        (fun slot => binaryCovector mask (maskIndex chunk slot)) := by
  rw [deferredMaskWeight, two_halves_eq_quarter]
  unfold deferredMaskSum dualWeightFoldValue
  rw [Fin.sum_univ_four]
  cases h0 : mask (maskIndex chunk 0) <;>
    cases h1 : mask (maskIndex chunk 1) <;>
    cases h2 : mask (maskIndex chunk 2) <;>
    cases h3 : mask (maskIndex chunk 3) <;>
    simp [deferredPower, binaryCovector, h0, h1, h2, h3]

/-- Flat index equations needed to connect the 64-by-four folded source
representation to its 64-by-sixteen pre-fold representation. -/
theorem grouped_index_arithmetic (row : Fin 64) (chunk slot : Fin 4) :
    (4 * row.val + chunk.val) / 4 = row.val ∧
    (4 * row.val + chunk.val) % 4 = chunk.val ∧
    (4 * (4 * row.val + chunk.val) + slot.val) / 16 = row.val ∧
    (4 * (4 * row.val + chunk.val) + slot.val) % 16 =
      4 * chunk.val + slot.val := by
  omega

/-- Full dot product of a sum of components is the sum of their dots. This
lets the proof connect each real `weight_at` constructor separately. -/
theorem component_sum_dot {I C : Type*} [Fintype I] [Fintype C]
    (values : I → K) (components : C → I → K) :
    (∑ i, values i * ∑ c, components c i) =
      ∑ c, ∑ i, values i * components c i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Source pointwise field reflection is sufficient to transport the full
sum; no equality of entire WeightAccumulator representations is required. -/
theorem full_dot_of_pointwise {I : Type*} [Fintype I]
    (values left right : I → K) (pointwise : ∀ i, left i = right i) :
    (∑ i, values i * left i) = ∑ i, values i * right i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [pointwise i]

/-- No-op observer calculations do not introduce a new terminal vector:
this is the exact mathematical discrepancy on all 256 entries. -/
theorem observer_discrepancy_of_weight_reflection
    (claim : K) (values sourceWeight modelWeight : Fin 256 → K)
    (reflection : ∀ i, sourceWeight i = modelWeight i) :
    claim - (∑ i, values i * sourceWeight i) =
      claim - candidateClaim modelWeight values := by
  unfold candidateClaim
  rw [full_dot_of_pointwise values sourceWeight modelWeight reflection]

/-- Algebraic diagnostic: a coefficient outside the first four can change
this observer value. No premise says later coefficients are zero. -/
theorem dot_change_single_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (values weights : I → K) (index : I) (delta : K) :
    (∑ i, (values i + if i = index then delta else 0) * weights i) =
      (∑ i, values i * weights i) + delta * weights index := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp

#print axioms deferredMaskWeight_eq_dualFold
#print axioms grouped_index_arithmetic
#print axioms component_sum_dot
#print axioms observer_discrepancy_of_weight_reflection
#print axioms dot_change_single_coordinate
end
end AspisK1.V7Tag73PrequeryWeights256
