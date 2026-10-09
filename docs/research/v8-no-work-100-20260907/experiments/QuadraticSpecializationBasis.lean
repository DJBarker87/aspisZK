import QuadraticSpecializationDeterminant
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
Construct the constant invertible basis change used by the determinant
multiplicity lemma.  No caller-supplied matrix inverse or existence-of-basis
premise is used.  The next Sylvester consumer must provide its actual
independent kernel vectors, not merely a zero determinant.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSpecializationBasis
noncomputable section
open Module Polynomial
open scoped Matrix

/-- Extend an arbitrary independent family to an invertible column matrix,
retaining each supplied vector at an injectively selected literal column. -/
theorem exists_invertible_columns
    {K I J : Type*} [Field K] [Fintype I] [DecidableEq I]
    (v : J → I → K) (independent : LinearIndependent K v) :
    ∃ (B : Matrix I I K) (select : J → I),
      B.det ≠ 0 ∧ Function.Injective select ∧
        ∀ j i, B i (select j) = v j i := by
  classical
  let extension : Set (I → K) :=
    independent.linearIndepOn_id.extend (Set.subset_univ (Set.range v))
  let b : Basis extension K (I → K) := Basis.extend independent.linearIndepOn_id
  let embedding : J → extension := fun j =>
    ⟨v j, independent.linearIndepOn_id.subset_extend _ (Set.mem_range_self j)⟩
  have embeddingInjective : Function.Injective embedding := by
    intro i j equal
    apply independent.injective
    exact congrArg Subtype.val equal
  let index : extension ≃ I := b.indexEquiv (Pi.basisFun K I)
  let b' : Basis I K (I → K) := b.reindex index
  let select : J → I := fun j => index (embedding j)
  have selectedVector : ∀ j, b' (select j) = v j := by
    intro j
    change (b.reindex index) (index (embedding j)) = v j
    rw [Basis.reindex_apply, Equiv.symm_apply_apply]
    exact Basis.extend_apply_self independent.linearIndepOn_id (embedding j)
  let B : Matrix I I K := (Pi.basisFun K I).toMatrix b'
  have inverse : B * b'.toMatrix (Pi.basisFun K I) = 1 :=
    Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun K I) b'
  have determinantNonzero : B.det ≠ 0 := by
    intro determinantZero
    have determinants := congrArg Matrix.det inverse
    simp only [Matrix.det_mul, Matrix.det_one, determinantZero, zero_mul] at determinants
    exact zero_ne_one determinants
  refine ⟨B, select, determinantNonzero, index.injective.comp embeddingInjective, ?_⟩
  intro j i
  change (b' (select j)) i = v j i
  rw [selectedVector]

/-- Actual independent specialized kernel vectors imply root multiplicity
of the determinant.  The invertible matrix is constructed in the proof. -/
theorem independent_kernel_pow_dvd_det
    {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I I K[X]) (gamma : K) (v : J → I → K)
    (independent : LinearIndependent K v)
    (kernel : ∀ j, (Polynomial.evalRingHom gamma).mapMatrix M *ᵥ v j = 0) :
    (Polynomial.X - Polynomial.C gamma) ^ Fintype.card J ∣ M.det := by
  classical
  obtain ⟨B, select, determinantNonzero, selectInjective, selectedVector⟩ :=
    exists_invertible_columns v independent
  let S : Finset I := Finset.univ.image select
  have cardSelected : S.card = Fintype.card J := by
    exact (Finset.card_image_of_injective Finset.univ selectInjective).trans
      (Finset.card_univ)
  have actualKernel : ∀ j ∈ S, ∀ i,
      ((Polynomial.evalRingHom gamma).mapMatrix M * B) i j = 0 := by
    intro j member i
    obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp member
    have vectorZero := congrFun (kernel source) i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      selectedVector, Pi.zero_apply] using vectorZero
  have multiplicity := QuadraticSpecializationDeterminant.kernel_columns_pow_dvd_det
    M B gamma S determinantNonzero actualKernel
  rwa [cardSelected] at multiplicity

#print axioms exists_invertible_columns
#print axioms independent_kernel_pow_dvd_det

end
end AspisV8.QuadraticSpecializationBasis
