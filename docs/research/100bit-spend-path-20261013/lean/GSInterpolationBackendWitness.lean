import GSInterpolationRowBasis
import GSConstraintCount
import GSInterpolationBudget
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness

open CompPoly
open CompPoly.CBivariate
open CompPoly.GuruswamiSudan

namespace AspisWide.GSInterpolationBackendWitness

private def initialParams : GSInterpParams := ⟨1025, 3, 114689⟩
private def finalParams : GSInterpParams := ⟨256, 3, 28673⟩

private theorem initialBasis_size :
    (AspisWide.GSInterpolationRowBasis.basis 1024 114689 112).size = 6480098 := by
  rw [AspisWide.GSInterpolationRowBasis.basis_size,
    AspisWide.GSInterpolationRowBasis.rowCount_eq_weightedMonomialCount 1024 114689 112
      (by norm_num : 1024 * 112 ≤ 114689)]
  exact AspisWide.GSInterpolationBudget.initial_weighted_count

private theorem finalBasis_size :
    (AspisWide.GSInterpolationRowBasis.basis 255 28673 112).size = 1626522 := by
  rw [AspisWide.GSInterpolationRowBasis.basis_size,
    AspisWide.GSInterpolationRowBasis.rowCount_eq_weightedMonomialCount 255 28673 112
      (by norm_num : 255 * 112 ≤ 28673)]
  exact AspisWide.GSInterpolationBudget.final_weighted_count

private theorem initialBasis_nodup :
    (AspisWide.GSInterpolationRowBasis.basis 1024 114689 112).toList.Nodup :=
  AspisWide.GSInterpolationRowBasis.basis_nodup _ _ _

private theorem finalBasis_nodup :
    (AspisWide.GSInterpolationRowBasis.basis 255 28673 112).toList.Nodup :=
  AspisWide.GSInterpolationRowBasis.basis_nodup _ _ _

private theorem initialBasis_bound (m : CBivariate.Monomial)
    (hm : m ∈ (AspisWide.GSInterpolationRowBasis.basis 1024 114689 112).toList) :
    1 * m.xDegree + 1024 * m.yDegree ≤ 114689 := by
  change m ∈ (AspisWide.GSInterpolationRowBasis.rows 1024 114689 112).toArray.toList at hm
  rw [List.toList_toArray] at hm
  simpa only [one_mul] using
    (AspisWide.GSInterpolationRowBasis.row_weighted_bound 1024 114689 112
      (by norm_num : 1024 * 112 ≤ 114689) hm)

private theorem finalBasis_bound (m : CBivariate.Monomial)
    (hm : m ∈ (AspisWide.GSInterpolationRowBasis.basis 255 28673 112).toList) :
    1 * m.xDegree + 255 * m.yDegree ≤ 28673 := by
  change m ∈ (AspisWide.GSInterpolationRowBasis.rows 255 28673 112).toArray.toList at hm
  rw [List.toList_toArray] at hm
  simpa only [one_mul] using
    (AspisWide.GSInterpolationRowBasis.row_weighted_bound 255 28673 112
      (by norm_num : 255 * 112 ≤ 28673) hm)

/-- Actual executable dense-backend interpolation witness for the initial WideExact-sized word. -/
theorem initial_dense_witness {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
    (points : Array (K × K)) (hsize : points.size = 1048576) :
    ∃ Q, denseInterpolateWithBasisAndKernel (denseLinearKernelContext K)
      (AspisWide.GSInterpolationRowBasis.basis 1024 114689 112) points initialParams = some Q ∧
      ValidInterpolationWitness points initialParams Q := by
  rcases denseInterpolateWithBasis_exists_of_dimension_slack
      (basis := AspisWide.GSInterpolationRowBasis.basis 1024 114689 112)
      points initialParams (by
        change (interpolationConstraints points 3).size <
          (AspisWide.GSInterpolationRowBasis.basis 1024 114689 112).size
        rw [AspisWide.GSConstraintCount.interpolationConstraints_size_three, hsize, initialBasis_size]
        norm_num) with ⟨Q, hQ⟩
  refine ⟨Q, hQ, ?_⟩
  exact denseInterpolateWithBasisAndKernel_sound_of_bounded_basis
    (kernelContext := denseLinearKernelContext K)
    initialBasis_nodup initialBasis_bound hQ

/-- Actual executable dense-backend interpolation witness for the final WideExact-sized word. -/
theorem final_dense_witness {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
    (points : Array (K × K)) (hsize : points.size = 262144) :
    ∃ Q, denseInterpolateWithBasisAndKernel (denseLinearKernelContext K)
      (AspisWide.GSInterpolationRowBasis.basis 255 28673 112) points finalParams = some Q ∧
      ValidInterpolationWitness points finalParams Q := by
  rcases denseInterpolateWithBasis_exists_of_dimension_slack
      (basis := AspisWide.GSInterpolationRowBasis.basis 255 28673 112)
      points finalParams (by
        change (interpolationConstraints points 3).size <
          (AspisWide.GSInterpolationRowBasis.basis 255 28673 112).size
        rw [AspisWide.GSConstraintCount.interpolationConstraints_size_three, hsize, finalBasis_size]
        norm_num) with ⟨Q, hQ⟩
  refine ⟨Q, hQ, ?_⟩
  exact denseInterpolateWithBasisAndKernel_sound_of_bounded_basis
    (kernelContext := denseLinearKernelContext K)
    finalBasis_nodup finalBasis_bound hQ

#print axioms initial_dense_witness
#print axioms final_dense_witness

end AspisWide.GSInterpolationBackendWitness
