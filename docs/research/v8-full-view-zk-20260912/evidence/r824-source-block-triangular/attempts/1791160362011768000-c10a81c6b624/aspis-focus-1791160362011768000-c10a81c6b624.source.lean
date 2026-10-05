import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R816Fin222ActiveSupplementDispatch
import AspisV8R19.R823ActiveLowerZeroDispatcher
import AspisV8R19.R828SupplementarySourceLowerRows
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R824SourceBlockTriangular
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R766BlockOrderEquivalences
open AspisV8R19.R816Fin222ActiveSupplementDispatch
open AspisV8R19.R823ActiveLowerZeroDispatcher
open AspisV8R19.R828SupplementarySourceLowerRows

noncomputable section

theorem active_lowerRow (i : Fin 214) : lowerRow (activePos i) := by
  intro j hj
  have hz := active_row_lower_zero i j hj
  change fixedSourceMatrix (rowOrder (rowOrderInv (activePosition i))) (colOrder j) = 0
  rw [row_right]
  exact hz

theorem source_block_triangular : reorderedSourceMatrix.BlockTriangular blockLabel := by
  change ∀ ⦃i j : Fin 222⦄, blockLabel j < blockLabel i →
    reorderedSourceMatrix i j = 0
  intro i j hij
  have hall : ∀ r : Fin 222, lowerRow r :=
    fin222_from_active_and_supplement active_lowerRow supplementary_lowerRow
  have hraw : blockLabel j < blockLabel (rowOrderInv (rowOrder i)) := by
    rw [row_left]
    exact hij
  have hz := hall (rowOrder i) (j := j) hraw
  simpa [reorderedSourceMatrix, row_left] using hz

#print axioms active_lowerRow
#print axioms source_block_triangular
end
end AspisV8R19.R824SourceBlockTriangular
