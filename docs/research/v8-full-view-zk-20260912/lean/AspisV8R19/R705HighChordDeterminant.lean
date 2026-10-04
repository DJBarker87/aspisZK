import AspisV8R19.R702ActiveScalarEmbedding
import AspisV8R19.R703ActiveBlockMatrix
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R705HighChordDeterminant
open R702ActiveScalarEmbedding R703ActiveBlockMatrix AspisV8R17
noncomputable section
local instance : DecidablePred zero := fun i => inferInstanceAs (Decidable (i.val.val % 4 = 0))
variable {F : Type*} [Field F]

def scalarMatrix (half : F) : Matrix High High F := fun i j =>
  sourceChord half (chosenQ (Pi.single j 1)) 2 0 0 i.val.val

theorem scalarMatrix_eq (half : F) :
    scalarMatrix half = (2:F) • blockMatrix block zero := by
  ext i j
  rw [scalarMatrix,scalar_chord_row,← mulVec_block]
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,Matrix.smul_apply,blockMatrix]

theorem scalarMatrix_det_ne_zero (half : F) (h2 : (2:F) ≠ 0) :
    (scalarMatrix half).det ≠ 0 := by
  rw [scalarMatrix_eq,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ h2)
    (blockMatrix_det_ne_zero block zero zero_unique)

def polyMatrix (half : F) : Matrix High High (Polynomial F) := fun i j =>
  Polynomial.C (scalarMatrix half i j) + Polynomial.X *
    Polynomial.C (sourceChord half (chosenQ (Pi.single j 1)) 0 0 1 i.val.val)

theorem polyMatrix_eval_zero (half : F) :
    (Polynomial.evalRingHom 0).mapMatrix (polyMatrix half) = scalarMatrix half := by
  ext i j
  simp [polyMatrix]

theorem polyMatrix_det_eval_zero (half : F) (h2 : (2:F) ≠ 0) :
    (polyMatrix half).det.eval 0 ≠ 0 := by
  have h := (Polynomial.evalRingHom (0:F)).map_det (polyMatrix half)
  rw [polyMatrix_eval_zero] at h
  change (polyMatrix half).det.eval 0 = (scalarMatrix half).det at h
  rw [h]
  exact scalarMatrix_det_ne_zero half h2

theorem polyMatrix_det_ne_zero (half : F) (h2 : (2:F) ≠ 0) :
    (polyMatrix half).det ≠ 0 := by
  intro h
  have he := polyMatrix_det_eval_zero half h2
  rw [h] at he
  exact he (by simp)

#print axioms scalarMatrix_eq
#print axioms scalarMatrix_det_ne_zero
#print axioms polyMatrix_eval_zero
#print axioms polyMatrix_det_eval_zero
#print axioms polyMatrix_det_ne_zero
end
end AspisV8R19.R705HighChordDeterminant
