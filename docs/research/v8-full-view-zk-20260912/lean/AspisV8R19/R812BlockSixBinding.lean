import AspisV8R19.R816BlockSixSourceView
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R812SourceBlock06Binding
import AspisV8R19.R812SourceBlock06RowsChunk00
import AspisV8R19.R812Rows01
import AspisV8R19.R812Rows02
import AspisV8R19.R812Rows03
import AspisV8R19.R812Rows04
import AspisV8R19.R812Rows05
import AspisV8R19.R812Rows06
import AspisV8R19.R812Rows07
import AspisV8R19.R812Rows08
import AspisV8R19.R812BlockSixP2RowBridge
import AspisV8R19.R812BlockSixP0RowBridge
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812BlockSixBinding
open AspisV8R19.R816BlockSixSourceView AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R812BlockSixP2RowBridge AspisV8R19.R812BlockSixP0RowBridge
noncomputable section
theorem source_block06_eq_certificate : diagonalSourceBlock 6 = R747JointBlock39Preflight.A := by
  funext i
  fin_cases i
  · funext j; exact AspisV8R19.R812SourceBlock06Binding.source_block06_row0 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk00.source_block06_active_row_local01 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk00.source_block06_active_row_local02 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk00.source_block06_active_row_local03 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk00.source_block06_active_row_local04 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk01.source_block06_active_row_local05 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk01.source_block06_active_row_local06 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk01.source_block06_active_row_local07 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk01.source_block06_active_row_local08 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk02.source_block06_active_row_local09 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk02.source_block06_active_row_local10 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk02.source_block06_active_row_local11 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk02.source_block06_active_row_local12 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk03.source_block06_active_row_local13 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk03.source_block06_active_row_local14 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk03.source_block06_active_row_local15 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk03.source_block06_active_row_local16 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk04.source_block06_active_row_local17 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk04.source_block06_active_row_local18 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk04.source_block06_active_row_local19 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk04.source_block06_active_row_local20 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk05.source_block06_active_row_local21 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk05.source_block06_active_row_local22 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk05.source_block06_active_row_local23 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk05.source_block06_active_row_local24 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk06.source_block06_active_row_local25 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk06.source_block06_active_row_local26 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk06.source_block06_active_row_local27 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk06.source_block06_active_row_local28 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk07.source_block06_active_row_local29 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk07.source_block06_active_row_local30 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk07.source_block06_active_row_local31 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk07.source_block06_active_row_local32 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk08.source_block06_active_row_local33 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk08.source_block06_active_row_local34 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk08.source_block06_active_row_local35 j
  · funext j; exact AspisV8R19.R812SourceBlock06RowsChunk08.source_block06_active_row_local36 j
  · rw [diagonalSourceBlock06_eq_sourceView]
    change (fun j : Fin 39 => fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 2) (block06Columns j)) = _
    exact p2_source_row_eq_certificate
  · rw [diagonalSourceBlock06_eq_sourceView]
    change (fun j : Fin 39 => fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 0) (block06Columns j)) = _
    exact p0_source_row_eq_certificate
#print axioms source_block06_eq_certificate
end
end AspisV8R19.R812BlockSixBinding
