import AspisV8R19.('R807SourceBlock03Row00', 'source_block03_row00')
import AspisV8R19.('R807SourceBlock03RowsChunk00', 'source_block03_row01')
import AspisV8R19.('R807SourceBlock03RowsChunk00', 'source_block03_row02')
import AspisV8R19.('R807SourceBlock03RowsChunk01', 'source_block03_row03')
import AspisV8R19.('R807SourceBlock03RowsChunk01', 'source_block03_row04')
import AspisV8R19.('R807SourceBlock03RowsChunk02', 'source_block03_row05')
import AspisV8R19.('R807SourceBlock03RowsChunk02', 'source_block03_row06')
import AspisV8R19.('R807SourceBlock03RowsChunk03', 'source_block03_row07')
import AspisV8R19.R752SCC03Matrix
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock03Binding
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
noncomputable section

theorem source_block03_eq_certificate : diagonalSourceBlock 3 = R752SCC03Matrix.A_scc := by
  ext i j
  fin_cases i
  · exact congrFun AspisV8R19.R807SourceBlock03Row00.source_block03_row00 j
  · exact congrFun AspisV8R19.R807SourceBlock03RowsChunk00.source_block03_row01 j
  · exact congrFun AspisV8R19.R807SourceBlock03RowsChunk00.source_block03_row02 j
  · exact congrFun AspisV8R19.R807SourceBlock03RowsChunk01.source_block03_row03 j
  · exact congrFun AspisV8R19.R807SourceBlock03RowsChunk01.source_block03_row04 j
  · exact congrFun AspisV8R19.R807SourceBlock03RowsChunk02.source_block03_row05 j
  · exact congrFun AspisV8R19.R807SourceBlock03RowsChunk02.source_block03_row06 j
  · exact congrFun AspisV8R19.R807SourceBlock03RowsChunk03.source_block03_row07 j
#print axioms source_block03_eq_certificate
end

end AspisV8R19.R807SourceBlock03Binding
