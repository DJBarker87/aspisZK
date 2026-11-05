import NGK_COMBINED_IMPORT
import NGO_COMBINED_IMPORT
import NGV_AtPacket
import NGV_AtSubstitution
import NGV_ByteWindow
import NGV_ChunkCheck
import NGV_ChunkPredicate
import NGV_ChunkTail
import NGV_ChunkWords
import NGV_Cursors
import NGV_DecodeAfterParse
import NGV_ExpandAssociation
import NGV_ExpandPacket
import NGV_Monad
import NGV_ParsePacket
import NGV_ParseSubstitution
import NGV_Payload
import NGV_PrefixWindow
import NGV_RowFrame
import NGV_RowPayload
import NGV_RowValues
import NGV_SemanticArithmetic
import NGV_SemanticCut
import NGV_SemanticDomains
import NGV_SemanticFrames
import NGV_SemanticHeader
import NGV_SemanticHigh
import NGV_SemanticInitial
import NGV_SemanticLow
import NGV_SemanticPacket
import NGV_SemanticStep
import NGV_SemanticTrace
import NGV_SemanticValues
import NGV_Validator
import NGV_ValidatorLoop
import NGV_ValidatorStep
import NGV_ValidatorTotal
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NGV_AtPacket.result
#print axioms NGV_AtSubstitution.congr
#print axioms NGV_ByteWindow.select_length
#print axioms NGV_ByteWindow.write_length
#print axioms NGV_ByteWindow.read
#print axioms NGV_ByteWindow.read_mut
#print axioms NGV_ByteWindow.copy
#print axioms NGV_ChunkCheck.result
#print axioms NGV_ChunkPredicate.word
#print axioms NGV_ChunkPredicate.valid
#print axioms NGV_ChunkTail.exact_chunks
#print axioms NGV_ChunkTail.construct
#print axioms NGV_ChunkWords.parse
#print axioms NGV_Cursors.source_add
#print axioms NGV_Cursors.output_add
#print axioms NGV_Cursors.advance
#print axioms NGV_DecodeAfterParse.result
#print axioms NGV_ExpandAssociation.result
#print axioms NGV_ExpandPacket.result
#print axioms NGV_Monad.bind_congr
#print axioms NGV_Monad.bind_congr_on
#print axioms NGV_ParsePacket.result
#print axioms NGV_ParseSubstitution.congr
#print axioms NGV_Payload.selected
#print axioms NGV_PrefixWindow.read
#print axioms NGV_PrefixWindow.read_mut
#print axioms NGV_RowFrame.outside
#print axioms NGV_RowFrame.later
#print axioms NGV_RowPayload.domains
#print axioms NGV_RowPayload.construct
#print axioms NGV_RowPayload.length
#print axioms NGV_RowValues.header
#print axioms NGV_RowValues.payload
#print axioms NGV_SemanticArithmetic.add
#print axioms NGV_SemanticArithmetic.div
#print axioms NGV_SemanticArithmetic.next
#print axioms NGV_SemanticCut.cut
#print axioms NGV_SemanticDomains.row
#print axioms NGV_SemanticFrames.length
#print axioms NGV_SemanticFrames.preserved_prefix
#print axioms NGV_SemanticHeader.result
#print axioms NGV_SemanticHigh.result
#print axioms NGV_SemanticInitial.compact_length
#print axioms NGV_SemanticInitial.logical_length
#print axioms NGV_SemanticInitial.rows
#print axioms NGV_SemanticInitial.bind_assoc
#print axioms NGV_SemanticInitial.emitted
#print axioms NGV_SemanticInitial.copied
#print axioms NGV_SemanticLow.result
#print axioms NGV_SemanticPacket.result
#print axioms NGV_SemanticPacket.intervals
#print axioms NGV_SemanticPacket.coverage
#print axioms NGV_SemanticStep.result
#print axioms NGV_SemanticTrace.construct
#print axioms NGV_SemanticTrace.result
#print axioms NGV_SemanticValues.rows
#print axioms NGV_Validator.result
#print axioms NGV_ValidatorLoop.window
#print axioms NGV_ValidatorLoop.result
#print axioms NGV_ValidatorStep.cut
#print axioms NGV_ValidatorStep.step
#print axioms NGV_ValidatorTotal.result
