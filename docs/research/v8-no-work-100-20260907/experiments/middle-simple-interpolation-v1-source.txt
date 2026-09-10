import AspisFormal.K1.V7ExactCorrelatedAgreementInterpolation

/-! Multiplicity-one, middle-support-only auxiliary interpolation.
The old multiplicity-three selector is not changed. These coefficients are
chosen from the fixed received lane array, before OOD, gamma, or candidates.
The large linear system is used only through its symbolic dimension; this
file does not construct or enumerate its matrix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.MiddleSimpleInterpolation
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementInterpolation
noncomputable section
variable {K : Type*} [Field K]

/-- Only the (0,0) Hasse constraint is required. The codomain has n*zBound
entries, not the sixfold multiplicity-three codomain. -/
def simpleMap {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (points : Fin n → K) (lanes : Fin (curveDegree + 1) → Fin n → K) :
    (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) →ₗ[K]
      (Fin n → Fin zBound → K) where
  toFun coefficients i j := curveInterpolationMap points lanes coefficients i 0 j
  map_add' left right := by
    funext i j
    simp only [map_add, Pi.add_apply]
  map_smul' scalar coefficients := by
    funext i j
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem two_rows_count (maximumDegree curveDegree xBound zBound : Nat) :
    curveMonomialCount maximumDegree curveDegree xBound 2 zBound =
      xBound*zBound+(xBound-maximumDegree)*(zBound-curveDegree) := by
  simp [curveMonomialCount, Finset.sum_range_succ]

/-- Every integer operation is a closed-form two-row calculation; no
million-element Finset or recurrence is evaluated. -/
theorem middle_dimension :
    curveMonomialCount 1024 28 803230 2 41 = 43361108 ∧
      1048576*41 = 42991616 ∧
      1048576*41 < curveMonomialCount 1024 28 803230 2 41 := by
  rw [two_rows_count]
  norm_num

theorem exists_nonzero_simple_kernel
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (points : Fin n → K) (lanes : Fin (curveDegree + 1) → Fin n → K)
    (dimension : n*zBound <
      curveMonomialCount maximumDegree curveDegree xBound yRows zBound) :
    ∃ coefficients : CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K,
      coefficients ≠ 0 ∧ simpleMap points lanes coefficients = 0 := by
  let constraints := simpleMap (maximumDegree := maximumDegree) (xBound := xBound)
    (yRows := yRows) (zBound := zBound) points lanes
  have codomainRank : Module.finrank K (Fin n → Fin zBound → K) = n*zBound := by
    simp only [Module.finrank_pi_fintype, Finset.sum_const, nsmul_eq_mul,
      Fintype.card_fin, Finset.card_univ, Module.finrank_self]
    ring
  have domainRank : Module.finrank K
      (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) =
      curveMonomialCount maximumDegree curveDegree xBound yRows zBound := by
    rw [Module.finrank_pi, curveMonomialIndex_card]
  have rankLess : Module.finrank K (Fin n → Fin zBound → K) <
      Module.finrank K
        (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) := by
    rw [codomainRank, domainRank]
    exact dimension
  have nontrivialKernel : LinearMap.ker constraints ≠ ⊥ :=
    constraints.ker_ne_bot_of_finrank_lt rankLess
  rw [Submodule.ne_bot_iff] at nontrivialKernel
  obtain ⟨coefficients, member, nonzero⟩ := nontrivialKernel
  exact ⟨coefficients, nonzero, LinearMap.mem_ker.mp member⟩

/-- The one retained Hasse constraint vanishes identically in gamma, not
only at sampled values. This is the input to the next candidate-root leaf. -/
theorem constraint_zero {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (positive : 0 < zBound) (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (kernel : simpleMap points lanes coefficients = 0) (index : Fin n) :
    curveConstraintPolynomial points lanes coefficients index 0 = 0 := by
  ext degree
  by_cases bounded : degree < zBound
  · let j : Fin zBound := ⟨degree, bounded⟩
    rw [show degree = j.val from rfl, curveConstraintPolynomial_coeff]
    have pointwise := congrFun (congrFun kernel index) j
    change curveInterpolationMap points lanes coefficients index 0 j = 0 at pointwise
    exact pointwise
  · have degreeBound := curveConstraintPolynomial_natDegree_lt positive
      points lanes coefficients index 0
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le degreeBound (Nat.le_of_not_gt bounded)), Polynomial.coeff_zero]

/-- A pre-OOD selector may choose this nonempty kernel using only the
fixed 29 received lanes. No source polynomiality or adaptive candidate is
an input to existence. -/
theorem exists_middle_interpolant (points : Fin 1048576 → K)
    (lanes : Fin 29 → Fin 1048576 → K) :
    ∃ coefficients : CurveMonomialIndex 1024 28 803230 2 41 → K,
      coefficients ≠ 0 ∧ simpleMap points lanes coefficients = 0 :=
  exists_nonzero_simple_kernel points lanes middle_dimension.2.2

#print axioms two_rows_count
#print axioms middle_dimension
#print axioms exists_nonzero_simple_kernel
#print axioms constraint_zero
#print axioms exists_middle_interpolant
end
end AspisV8.MiddleSimpleInterpolation
