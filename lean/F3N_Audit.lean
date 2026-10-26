import F3N_AuthenticatedTen
import F3N_BatchCode
import F3N_BatchMapLog
import F3N_BatchMapReturn
import F3N_BatchPhysical
import F3N_BatchPrograms
import F3N_CheckpointLog
import F3N_CheckpointRun
import F3N_CircleCoordinates
import F3N_CircleProjection
import F3N_ClaimCell
import F3N_ClaimPolynomial
import F3N_ClaimRowSum
import F3N_ClaimShape
import F3N_ConsDictionary
import F3N_ConsSource
import F3N_ContextCoordinates
import F3N_CoordinateShape
import F3N_CurrentBatchPrograms
import F3N_FinishLog
import F3N_FinishValue
import F3N_LeafLog
import F3N_ModelBody
import F3N_NativeSource
import F3N_OrderedSum
import F3N_OriginalClaim
import F3N_P6LevelLog
import F3N_PairReadback
import F3N_PairTenFinish
import F3N_PairTenReader
import F3N_PairWriter
import F3N_PhysicalBind
import F3N_PhysicalCode
import F3N_PhysicalLevels
import F3N_PhysicalNode
import F3N_PhysicalRows
import F3N_PoolAccumulator
import F3N_Prepared
import F3N_PreparedCells
import F3N_PreparedClaim
import F3N_PreparedClaimSource
import F3N_PreparedCoordinates
import F3N_ProgramCarrier
import F3N_ReaderDiscovered
import F3N_ReaderNumeric
import F3N_ReaderPhysical
import F3N_SameOracle
import F3N_SameRun
import F3N_SameRunAccumulator
import F3N_SameRunTen
import F3N_SameRunWriter
import F3N_SameSecond
import F3N_SecondFinish
import F3N_SelectedDispatch
import F3N_SelectedScalar
import F3N_SourceCheckpointLog
import F3N_SourceEffect
import F3N_SourceInput
import F3N_SourceWriterLog
import F3N_Ten
import F3N_TenDiscovered
import F3N_TenInput
import F3N_WriterModel
import F3N_WriterNumeric
import F3N_WriterOnRun
import F3N_WriterReturned

/- Focused F3N object-union audit, not a frozen manifest or package replay. -/
#print axioms AspisR1.F3N_AuthenticatedTen.same_run
#print axioms AspisR1.F3N_BatchCode.raw
#print axioms AspisR1.F3N_BatchMapLog.log
#print axioms AspisR1.F3N_BatchMapReturn.accepted
#print axioms AspisR1.F3N_BatchPhysical.total
#print axioms AspisR1.F3N_BatchPhysical.stage
#print axioms AspisR1.F3N_BatchPhysical.current
#print axioms AspisR1.F3N_BatchPrograms.errors
#print axioms AspisR1.F3N_BatchPrograms.code_eq
#print axioms AspisR1.F3N_BatchPrograms.stage
#print axioms AspisR1.F3N_BatchPrograms.map_log
#print axioms AspisR1.F3N_CheckpointLog.stage
#print axioms AspisR1.F3N_CheckpointRun.exists_run
#print axioms AspisR1.F3N_CircleCoordinates.first
#print axioms AspisR1.F3N_CircleCoordinates.second
#print axioms AspisR1.F3N_CircleProjection.pair
#print axioms AspisR1.F3N_ClaimCell.successor
#print axioms AspisR1.F3N_ClaimPolynomial.polynomial
#print axioms AspisR1.F3N_ClaimRowSum.row
#print axioms AspisR1.F3N_ClaimShape.value
#print axioms AspisR1.F3N_ConsDictionary.dictionary
#print axioms AspisR1.F3N_ConsDictionary.digest
#print axioms AspisR1.F3N_ConsSource.from_cut
#print axioms AspisR1.F3N_ContextCoordinates.context
#print axioms AspisR1.F3N_CoordinateShape.coordinates
#print axioms AspisR1.F3N_CurrentBatchPrograms.code_eq
#print axioms AspisR1.F3N_CurrentBatchPrograms.log
#print axioms AspisR1.F3N_FinishLog.silent
#print axioms AspisR1.F3N_FinishLog.parent
#print axioms AspisR1.F3N_FinishLog.reads
#print axioms AspisR1.F3N_FinishValue.finish_value
#print axioms AspisR1.F3N_LeafLog.accepted
#print axioms AspisR1.F3N_ModelBody.body
#print axioms AspisR1.F3N_NativeSource.native
#print axioms AspisR1.F3N_OrderedSum.sum
#print axioms AspisR1.F3N_OriginalClaim.value
#print axioms AspisR1.F3N_P6LevelLog.source
#print axioms AspisR1.F3N_P6LevelLog.callbacks
#print axioms AspisR1.F3N_PairReadback.accepted
#print axioms AspisR1.F3N_PairTenFinish.accepted
#print axioms AspisR1.F3N_PairTenReader.accepted
#print axioms AspisR1.F3N_PairWriter.accepted
#print axioms AspisR1.F3N_PhysicalBind.bind
#print axioms AspisR1.F3N_PhysicalBind.pure
#print axioms AspisR1.F3N_PhysicalCode.transport
#print axioms AspisR1.F3N_PhysicalCode.bind
#print axioms AspisR1.F3N_PhysicalLevels.level
#print axioms AspisR1.F3N_PhysicalLevels.levels
#print axioms AspisR1.F3N_PhysicalNode.lift
#print axioms AspisR1.F3N_PhysicalNode.conditional
#print axioms AspisR1.F3N_PhysicalNode.parent
#print axioms AspisR1.F3N_PhysicalNode.node
#print axioms AspisR1.F3N_PhysicalRows.rows
#print axioms AspisR1.F3N_PoolAccumulator.accepted
#print axioms AspisR1.F3N_Prepared.equality
#print axioms AspisR1.F3N_PreparedCells.equality
#print axioms AspisR1.F3N_PreparedClaim.claim
#print axioms AspisR1.F3N_PreparedClaimSource.from_cut
#print axioms AspisR1.F3N_PreparedCoordinates.coordinates
#print axioms AspisR1.F3N_ProgramCarrier.total
#print axioms AspisR1.F3N_ReaderDiscovered.same_input
#print axioms AspisR1.F3N_ReaderNumeric.saved_ten
#print axioms AspisR1.F3N_ReaderPhysical.saved_ten
#print axioms AspisR1.F3N_SameOracle.current
#print axioms AspisR1.F3N_SameRun.accepted
#print axioms AspisR1.F3N_SameRunAccumulator.accepted
#print axioms AspisR1.F3N_SameRunTen.accepted
#print axioms AspisR1.F3N_SameRunWriter.accepted
#print axioms AspisR1.F3N_SameSecond.from_cut
#print axioms AspisR1.F3N_SecondFinish.from_calls
#print axioms AspisR1.F3N_SelectedDispatch.selected
#print axioms AspisR1.F3N_SelectedScalar.numeric
#print axioms AspisR1.F3N_SourceCheckpointLog.stage
#print axioms AspisR1.F3N_SourceEffect.accepted
#print axioms AspisR1.F3N_SourceInput.from_cut
#print axioms AspisR1.F3N_SourceWriterLog.writer_effects
#print axioms AspisR1.F3N_Ten.transport
#print axioms AspisR1.F3N_TenDiscovered.same_input
#print axioms AspisR1.F3N_TenInput.same_input
#print axioms AspisR1.F3N_WriterModel.saved
#print axioms AspisR1.F3N_WriterNumeric.saved
#print axioms AspisR1.F3N_WriterOnRun.saved
#print axioms AspisR1.F3N_WriterReturned.erased
