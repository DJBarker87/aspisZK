import AspisV8R19.R752SCC04Matrix
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R807SourceBlock04RowsChunk00
import AspisV8R19.R807SourceBlock04RowsChunk01
import AspisV8R19.R807SourceBlock04RowsChunk02
import AspisV8R19.R807SourceBlock04RowsChunk03
import AspisV8R19.R807SourceBlock04RowsChunk04
import AspisV8R19.R807SourceBlock04RowsChunk05
import AspisV8R19.R807SourceBlock04RowsChunk06
import AspisV8R19.R807SourceBlock04RowsChunk07
import AspisV8R19.R807SourceBlock04RowsChunk08
import AspisV8R19.R807SourceBlock04RowsChunk09
import AspisV8R19.R807SourceBlock04RowsChunk10
import AspisV8R19.R807SourceBlock04RowsChunk11
import AspisV8R19.R807SourceBlock04RowsChunk12
import AspisV8R19.R807SourceBlock04RowsChunk13
import AspisV8R19.R807SourceBlock04RowsChunk14
import AspisV8R19.R807SourceBlock04RowsChunk15
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock04Binding
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
noncomputable section

theorem source_block04_eq_certificate : diagonalSourceBlock 4 = R752SCC04Matrix.A_scc := by
  ext i j
  fin_cases i
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk00.source_block04_row00 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk01.source_block04_row01 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk02.source_block04_row02 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk03.source_block04_row03 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk04.source_block04_row04 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk05.source_block04_row05 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk06.source_block04_row06 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk07.source_block04_row07 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk08.source_block04_row08 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk09.source_block04_row09 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk10.source_block04_row10 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk11.source_block04_row11 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk12.source_block04_row12 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk13.source_block04_row13 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk14.source_block04_row14 j
  · exact congrFun AspisV8R19.R807SourceBlock04RowsChunk15.source_block04_row15 j
#print axioms source_block04_eq_certificate
end

end AspisV8R19.R807SourceBlock04Binding
