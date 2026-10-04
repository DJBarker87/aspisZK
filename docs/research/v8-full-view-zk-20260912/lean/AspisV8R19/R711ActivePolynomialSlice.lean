import AspisV8R19.R709ChosenColumnBasis
import AspisV8R19.R710SelectedActivePolynomial
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R711ActivePolynomialSlice
open AspisV8R17 R702ActiveScalarEmbedding R707FullActiveDeterminant
noncomputable section
variable {F : Type*} [Field F]

lemma column_at_one (j : R710SelectedActivePolynomial.J) :
    (fun r => unitVector (R710SelectedActivePolynomial.base j + R710SelectedActivePolynomial.slot j) r -
      unitVector (R710SelectedActivePolynomial.base j) r) = columnQ (F:=F) j := by
  funext r
  cases j with
  | inl j => exact (R709ChosenColumnBasis.chosenQ_single_basis j r).symm
  | inr j => simpa [R710SelectedActivePolynomial.base,R710SelectedActivePolynomial.slot,
      R710SelectedActivePolynomial.columnIndex,R698ActiveCoreLayout.extraTopColumn,columnQ]
      using (R709ChosenColumnBasis.extraQ_basis (F:=F) r).symm

lemma sourceMinor_one (half c : F) :
    R710SelectedActivePolynomial.sourceMinor half 1 2 0 c =
      (Polynomial.evalRingHom c).mapMatrix (fullMatrix half) := by
  apply Matrix.ext
  intro i j
  simp only [R710SelectedActivePolynomial.sourceMinor,one_pow,one_mul]
  rw [column_at_one]
  exact (polyChord_eval half c (columnQ j) (rowCode i)).symm

lemma determinant_slice (half u : F) (hu : u ≠ 0) :
    MvPolynomial.eval (activeAssignment 1 u u⁻¹)
      (R710SelectedActivePolynomial.polyMinor half).det =
      (fullMatrix half).det.eval (-(u+u⁻¹)) := by
  rw [R710SelectedActivePolynomial.determinant_eval]
  have ha : (1:F)+u*u⁻¹=2 := by rw [mul_inv_cancel₀ hu]; ring
  have hb : u*u⁻¹-1=0 := by rw [mul_inv_cancel₀ hu]; ring
  rw [ha,hb,sourceMinor_one]
  exact ((Polynomial.evalRingHom (-(u+u⁻¹))).map_det (fullMatrix half)).symm

#print axioms column_at_one
#print axioms sourceMinor_one
#print axioms determinant_slice
end
end AspisV8R19.R711ActivePolynomialSlice
