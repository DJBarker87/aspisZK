import AspisFormal.K1.V7ExactCorrelatedAgreementInterpolation

/-! A symbolic consumer of the already checked V7 dimension certificate.
The actual initial kernel has many projective directions for every received
word. No matrix is built, no monomial sum is replayed, and no selector is
identified with a convenient kernel member. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.InitialInterpolationKernelDimension
open Module
open AspisK1.V7ExactCorrelatedAgreementInterpolation

section Generic
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

theorem nullity_lower_bound (f : V →ₗ[K] W) :
    finrank K V ≤ finrank K W + finrank K (LinearMap.ker f) := by
  have rankNullity := f.finrank_range_add_finrank_ker
  have imageBound := (LinearMap.range f).finrank_le
  omega

/-- Even a chosen nonzero kernel element cannot span all possible choices.
Nonzeroness is unnecessary: the conclusion also excludes the zero generator. -/
theorem not_all_kernel_scalar (f : V →ₗ[K] W)
    (large : 1 < finrank K (LinearMap.ker f))
    (chosen : V) (chosenKernel : f chosen = 0) :
    ¬ ∀ other : V, f other = 0 → ∃ scalar : K, scalar • chosen = other := by
  intro allScalar
  have small : finrank K (LinearMap.ker f) ≤ 1 := by
    apply (finrank_le_one_iff).mpr
    refine ⟨⟨chosen, chosenKernel⟩, ?_⟩
    intro other
    obtain ⟨scalar, same⟩ := allScalar other.1 other.2
    exact ⟨scalar, Subtype.ext same⟩
  omega
end Generic

section Curve
variable {K : Type*} [Field K]

theorem curve_nullity_lower_bound
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (points : Fin n → K) (lanes : Fin (curveDegree + 1) → Fin n → K) :
    curveMonomialCount maximumDegree curveDegree xBound yRows zBound ≤
      6 * n * zBound + finrank K
        (LinearMap.ker (curveInterpolationMap (maximumDegree := maximumDegree)
          (xBound := xBound) (yRows := yRows) (zBound := zBound) points lanes)) := by
  have domainRank :
      finrank K (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) =
        curveMonomialCount maximumDegree curveDegree xBound yRows zBound := by
    rw [Module.finrank_pi, curveMonomialIndex_card]
  have codomainRank : finrank K (Fin n → Fin 6 → Fin zBound → K) =
      6 * n * zBound := by
    simp only [Module.finrank_pi_fintype, Finset.sum_const, nsmul_eq_mul,
      Fintype.card_fin, Finset.card_univ, Module.finrank_self]
    ring
  have bound := nullity_lower_bound
    (curveInterpolationMap (maximumDegree := maximumDegree) (xBound := xBound)
      (yRows := yRows) (zBound := zBound) points lanes)
  rw [domainRank, codomainRank] at bound
  exact bound

/-- Actual V7 initial dimensions, independent of the values of all lanes. -/
theorem initial_kernel_dimension (points : Fin 1048576 → K)
    (lanes : Fin 29 → Fin 1048576 → K) :
    15346221056 ≤ finrank K
      (LinearMap.ker (curveInterpolationMap (maximumDegree := 1024)
        (xBound := initialCurveXBound) (yRows := initialCurveYRows)
        (zBound := initialCurveZBound) points lanes)) := by
  have bound := curve_nullity_lower_bound (maximumDegree := 1024)
    (xBound := initialCurveXBound) (yRows := initialCurveYRows)
    (zBound := initialCurveZBound) points lanes
  have budget := exactInitialCurveInterpolationBudget
  rw [budget.1, budget.2.1] at bound
  omega

theorem initial_not_projective_unique (points : Fin 1048576 → K)
    (lanes : Fin 29 → Fin 1048576 → K)
    (chosen : CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
      initialCurveZBound → K)
    (chosenKernel : curveInterpolationMap points lanes chosen = 0) :
    ¬ ∀ other, curveInterpolationMap points lanes other = 0 →
      ∃ scalar : K, scalar • chosen = other := by
  apply not_all_kernel_scalar (curveInterpolationMap points lanes)
  · have large := initial_kernel_dimension points lanes
    omega
  · exact chosenKernel

end Curve

#print axioms nullity_lower_bound
#print axioms not_all_kernel_scalar
#print axioms curve_nullity_lower_bound
#print axioms initial_kernel_dimension
#print axioms initial_not_projective_unique
end AspisV8.InitialInterpolationKernelDimension
