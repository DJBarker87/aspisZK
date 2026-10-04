import AspisV8R19.R700ActiveBlockInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R703ActiveBlockMatrix
open R700ActiveBlockInverse
open scoped BigOperators
variable {I F : Type*} [Fintype I] [DecidableEq I] [CommRing F]
variable (block : I → Nat) (zero : I → Prop) [DecidablePred zero]

def blockMatrix : Matrix I I F := fun i j =>
  if zero i then (if block j=block i then -1 else 0) else (if j=i then 1 else 0)

theorem mulVec_block (x : I → F) :
    (blockMatrix block zero).mulVec x = blockTransform block zero x := by
  funext i
  by_cases hz : zero i
  · simp only [blockMatrix,Matrix.mulVec,dotProduct,if_pos hz,blockTransform]
    simp_rw [ite_mul,neg_one_mul,zero_mul]
    simp [blockRows,Finset.sum_filter,← Finset.sum_neg_distrib]
  · simp [blockMatrix,Matrix.mulVec,dotProduct,blockTransform,hz]

theorem blockMatrix_squared
    (unique : ∀ i j, zero i → zero j → block i=block j → i=j) :
    (blockMatrix block zero : Matrix I I F)*(blockMatrix block zero)=1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec,mulVec_block,mulVec_block,block_involution block zero unique]
  simp

variable [Nontrivial F]
theorem blockMatrix_det_ne_zero
    (unique : ∀ i j, zero i → zero j → block i=block j → i=j) :
    (blockMatrix block zero : Matrix I I F).det ≠ 0 := by
  have h := congrArg Matrix.det (blockMatrix_squared (F:=F) block zero unique)
  rw [Matrix.det_mul,Matrix.det_one] at h
  intro hz
  rw [hz,zero_mul] at h
  exact zero_ne_one h

#print axioms mulVec_block
#print axioms blockMatrix_squared
#print axioms blockMatrix_det_ne_zero
end AspisV8R19.R703ActiveBlockMatrix
