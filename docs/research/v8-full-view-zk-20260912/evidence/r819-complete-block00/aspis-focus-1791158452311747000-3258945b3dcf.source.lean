import AspisV8R19.R812SourceBlock00Cells00
import AspisV8R19.R813FinSixExt
import AspisV8R19.R814BlockZeroReindex
import AspisV8R19.R815BlockZeroSourceView
import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R810CoefficientCellPrototype
import AspisV8R19.R810CoefficientCellsChunk00
import AspisV8R19.R810CoefficientCellsChunk01
import AspisV8R19.R810CoefficientCellsChunk02
import AspisV8R19.R769Point1SelectedChunk06
import AspisV8R19.R752SCC00Inverse

set_option autoImplicit false
set_option maxRecDepth 32768
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R803LiteralSupplementaryEntries
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
namespace AspisV8R19.R812SourceBlock00Row00
noncomputable section

theorem source_block00_row00 : R815BlockZeroSourceView.block00SourceMatrix (⟨0,by omega⟩) = R752SCC00Matrix.A_scc (⟨0,by omega⟩) := by
  apply R813FinSixExt.fin6_ext
  all_goals simp only [R815BlockZeroSourceView.block00SourceMatrix, Matrix.submatrix_apply]
  · simpa only [R815BlockZeroSourceView.block00Rows, R814BlockZeroReindex.block00Columns, Matrix.cons_val_zero, Matrix.cons_val_succ] using R812SourceBlock00Cells00.source_cell_0_0
  · simpa only [R815BlockZeroSourceView.block00Rows, R814BlockZeroReindex.block00Columns, Matrix.cons_val_zero, Matrix.cons_val_succ] using R812SourceBlock00Cells00.source_cell_0_1
  · simpa only [R815BlockZeroSourceView.block00Rows, R814BlockZeroReindex.block00Columns, Matrix.cons_val_zero, Matrix.cons_val_succ] using R812SourceBlock00Cells00.source_cell_0_2
  · simpa only [R815BlockZeroSourceView.block00Rows, R814BlockZeroReindex.block00Columns, Matrix.cons_val_zero, Matrix.cons_val_succ] using R812SourceBlock00Cells00.source_cell_0_3
  · simpa only [R815BlockZeroSourceView.block00Rows, R814BlockZeroReindex.block00Columns, Matrix.cons_val_zero, Matrix.cons_val_succ] using R812SourceBlock00Cells00.source_cell_0_4
  · simpa only [R815BlockZeroSourceView.block00Rows, R814BlockZeroReindex.block00Columns, Matrix.cons_val_zero, Matrix.cons_val_succ] using R812SourceBlock00Cells00.source_cell_0_5
#print axioms source_block00_row00
end
end AspisV8R19.R812SourceBlock00Row00
