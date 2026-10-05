import AspisV8R19.R864SemanticKernel
import AspisV8R19.R867SemanticDirectionActiveKernel
import AspisV8R19.R866OrdinaryBlockKernel
import AspisV8R19.R825CompleteSourceDeterminant
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
namespace AspisV8R19.R870AugmentedSemanticDeterminant
open AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R864SemanticKernel
open AspisV8R19.R866OrdinaryBlockKernel
open AspisV8R19.R867SemanticDirectionActiveKernel
open scoped BigOperators
noncomputable section
abbrev Obs := R738JointObservationModel.ObservationRow
local instance : Fact (Nat.Prime 2147483647) := AspisV8R15.ExactTowerBase.m31PrimeFact
local instance : NeZero (2 : M) := ⟨by decide⟩
def extra : R738JointObservationModel.Index256 → M := indexedDirection 7 96 0

def semantic (q' : R738JointObservationModel.Index256 → M) : M :=
  ∑ i : Fin 271, maskWeights271 halfSelected semanticZ i *
    sourceChord halfSelected (rawFlatten q') (7:M) 5 (-5) (128+3*i.val)

def augmented : Matrix (Obs ⊕ Unit) (Obs ⊕ Unit) M :=
  Matrix.fromBlocks (chosenSourceMatrix halfSelected 536870912 7 2 3 5 0 z)
    (fun r (_ : Unit) => rawObservation halfSelected 536870912 7 5 (-5) 5 0 z extra r)
    (fun (_ : Unit) c => semantic (indexedDirection 7 (selectedColumns c).1 (selectedColumns c).2))
    (fun (_ : Unit) (_ : Unit) => semantic extra)

theorem block_det_factor {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (A : Matrix I I R) (B : Matrix Unit I R) (top : Matrix I Unit R)
    (delta : R) (htop : top = 0) :
    (Matrix.fromBlocks A top B (fun (_ : Unit) (_ : Unit) => delta)).det = A.det * delta := by
  rw [htop, Matrix.det_fromBlocks_zero₁₂]
  simp only [Matrix.det_unique]

theorem semantic_extra : semantic extra = 1610612604 := by
  unfold semantic extra
  rw [rawFlatten_indexedDirection]
  exact semantic_pairing

theorem extra_kernel_of_block_eq
    (hpoints : ∀ p : Fin 3, ∀ t : Fin 4,
      pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) (384+t.val) =
        pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) t.val)
    (row : Obs) : rawObservation halfSelected 536870912 7 5 (-5) 5 0 z extra row = 0 := by
  rcases row with j | ⟨p | k⟩
  · exact raw_active_zero halfSelected 536870912 7 5 (-5) 5 0 7 z j
  · unfold extra
    rw [rawObservation_indexedDirection]
    change (pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) 385 -
      7 * pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) 384) -
      (pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) 1 -
      7 * pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) 0) = 0
    have h1 := hpoints p (1 : Fin 4)
    have h0 := hpoints p (0 : Fin 4)
    change pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) 385 = _ at h1
    change pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) 384 = _ at h0
    rw [h1, h0]
    exact sub_self _
  · exact all_ordinary_coefficients_zero halfSelected 536870912 7 5 (-5) 5 0 7 z 96 0
      hpoints (relationIndex k)

theorem augmented_det_factor
    (hzero : ∀ row : Obs, rawObservation halfSelected 536870912 7 5 (-5) 5 0 z extra row = 0) :
    augmented.det = (chosenSourceMatrix halfSelected 536870912 7 2 3 5 0 z).det * 1610612604 := by
  classical
  have htop : (fun r (_ : Unit) =>
      rawObservation halfSelected 536870912 7 5 (-5) 5 0 z extra r) =
      (0 : Matrix Obs Unit M) := by
    funext r u
    exact hzero r
  have hf := block_det_factor
    (chosenSourceMatrix halfSelected 536870912 7 2 3 5 0 z)
    (fun (_ : Unit) c => semantic (indexedDirection 7 (selectedColumns c).1 (selectedColumns c).2))
    _ (semantic extra) htop
  change augmented.det = _ at hf
  rw [semantic_extra] at hf
  exact hf

theorem augmented_det_ne_zero_of_block_eq
    (hpoints : ∀ p : Fin 3, ∀ t : Fin 4,
      pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) (384+t.val) =
        pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) t.val) :
    augmented.det ≠ 0 := by
  rw [augmented_det_factor (extra_kernel_of_block_eq hpoints)]
  apply mul_ne_zero
  · exact R825CompleteSourceDeterminant.chosen_source_det_ne_zero
  · have h := semantic_pairing_ne_zero
    rw [semantic_pairing] at h
    exact h

#print axioms block_det_factor
#print axioms semantic_extra
#print axioms extra_kernel_of_block_eq
#print axioms augmented_det_factor
#print axioms augmented_det_ne_zero_of_block_eq
end
end AspisV8R19.R870AugmentedSemanticDeterminant
