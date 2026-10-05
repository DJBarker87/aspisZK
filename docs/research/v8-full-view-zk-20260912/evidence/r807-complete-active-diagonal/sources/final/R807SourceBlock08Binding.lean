import AspisV8R19.R752SCC08Matrix
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R807SourceBlock08RowsChunk00
import AspisV8R19.R807SourceBlock08RowsChunk01
import AspisV8R19.R807SourceBlock08RowsChunk02
import AspisV8R19.R807SourceBlock08RowsChunk03
import AspisV8R19.R813FiniteFunctionExt8

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock08Binding
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
noncomputable section

theorem source_block08_eq_certificate : diagonalSourceBlock 8 = R752SCC08Matrix.A_scc := by
  apply AspisV8R19.R813FiniteFunctionExt8.fin8_ext
  · exact AspisV8R19.R807SourceBlock08RowsChunk00.source_block08_row00
  · exact AspisV8R19.R807SourceBlock08RowsChunk00.source_block08_row01
  · exact AspisV8R19.R807SourceBlock08RowsChunk01.source_block08_row02
  · exact AspisV8R19.R807SourceBlock08RowsChunk01.source_block08_row03
  · exact AspisV8R19.R807SourceBlock08RowsChunk02.source_block08_row04
  · exact AspisV8R19.R807SourceBlock08RowsChunk02.source_block08_row05
  · exact AspisV8R19.R807SourceBlock08RowsChunk03.source_block08_row06
  · exact AspisV8R19.R807SourceBlock08RowsChunk03.source_block08_row07
#print axioms source_block08_eq_certificate
end

end AspisV8R19.R807SourceBlock08Binding
