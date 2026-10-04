import AspisV8R19.R710SelectedActivePolynomial
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R713FullActiveDegree
open R707FullActiveDeterminant R710SelectedActivePolynomial AspisV8R17
noncomputable section
variable {F : Type*} [Field F]

def linearMatrix (half : F) : Matrix J J F := fun i j =>
  sourceChord half (columnQ j) 0 0 1 (rowCode i)

def constantMatrix (half : F) : Matrix J J F := fun i j =>
  sourceChord half (columnQ j) 2 0 0 (rowCode i)

lemma fullMatrix_linear (half : F) :
    fullMatrix half = (Polynomial.X : Polynomial F) • (linearMatrix half).map Polynomial.C +
      (constantMatrix half).map Polynomial.C := by
  apply Matrix.ext
  intro i j
  simp only [fullMatrix,polyChord,linearMatrix,constantMatrix,Matrix.add_apply,
    Matrix.smul_apply,Matrix.map_apply,smul_eq_mul]
  ring

theorem full_det_degree (half : F) : (fullMatrix half).det.natDegree ≤ 214 := by
  rw [fullMatrix_linear]
  have h := Polynomial.natDegree_det_X_add_C_le (linearMatrix half) (constantMatrix half)
  rw [index_card] at h
  exact h

#print axioms fullMatrix_linear
#print axioms full_det_degree
end
end AspisV8R19.R713FullActiveDegree
