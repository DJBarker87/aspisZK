import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R805BlockDeterminantAssembly

set_option autoImplicit false
namespace AspisV8R19.R809SourceBlockAssembly
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R766BlockOrderEquivalences
noncomputable section

theorem diagonalSourceBlock_det (k : Fin 41) :
    (diagonalSourceBlock k).det = (reorderedSourceMatrix.toSquareBlock blockLabel k).det := by
  exact Matrix.det_submatrix_equiv_self (fiberEquiv k)
    (reorderedSourceMatrix.toSquareBlock blockLabel k)

theorem fixedSourceMatrix_det_unit_of_blocks
    (htri : reorderedSourceMatrix.BlockTriangular blockLabel)
    (hdiag : ∀ k : Fin 41, IsUnit (diagonalSourceBlock k).det) :
    IsUnit fixedSourceMatrix.det := by
  have hu : IsUnit reorderedSourceMatrix.det :=
    R805BlockDeterminantAssembly.blockTriangular_det_isUnit reorderedSourceMatrix blockLabel htri
      (fun k => by rw [← diagonalSourceBlock_det]; exact hdiag k)
  exact (R805BlockDeterminantAssembly.permuted_det_isUnit_iff fixedSourceMatrix rowEquiv colEquiv).mp hu

#print axioms diagonalSourceBlock_det
#print axioms fixedSourceMatrix_det_unit_of_blocks
end
end AspisV8R19.R809SourceBlockAssembly
