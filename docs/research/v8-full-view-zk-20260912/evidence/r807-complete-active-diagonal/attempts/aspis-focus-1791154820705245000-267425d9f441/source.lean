import AspisV8R19.R804LiteralSourceRowsChunk08
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R752SCC01Inverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk08
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

def fixedSourceMatrix : Matrix (Fin 222) (Fin 222) M :=
  literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected kappaSelected tauSelected z

def reorderedSourceMatrix : Matrix (Fin 222) (Fin 222) M :=
  fixedSourceMatrix.submatrix rowOrder colOrder

def diagonalSourceBlock (k : Fin 41) : Matrix (Fin (blockSize k)) (Fin (blockSize k)) M :=
  reorderedSourceMatrix.submatrix (flatIndex k) (flatIndex k)

theorem source_block01_eq_certificate : diagonalSourceBlock 1 = R752SCC01Matrix.A_scc := by
  ext i j
  fin_cases i
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨34,by decide⟩ : Fin 214))
    (colOrder (flatIndex 1 j)) = _
  rw [literalSourceMatrix_row184]
  fin_cases j
  rfl

theorem source_block01_det_unit : IsUnit (diagonalSourceBlock 1).det := by
  rw [source_block01_eq_certificate]
  exact R752SCC01Inverse.determinant_isUnit

#print axioms source_block01_eq_certificate
#print axioms source_block01_det_unit
end
end AspisV8R19.R807SourceBlock01Binding
