import NDI_BatchBridge
import NDI_BatchCaller
import NDI_BatchControl
import NDI_BatchInstalled
import NDI_BatchRef.Funs
import NDI_BatchRef.Types
import NDI_BatchRun
import NDI_BatchStep
import NDI_BatchWord
import NDI_BorrowBridge
import NDI_GeometryBridge
import NDI_GeometryRef.Funs
import NDI_GeometryRef.Types
import NDI_HeaderShifts
import NDI_IteratorFrame
import NDI_ParseShapeTail
import NDI_ParserAt
import NDI_ParserBody
import NDI_ParserHeader
import NDI_ParserInvalid
import NDI_ParserPayload
import NDI_ParserTotal
import NDI_PredicateLoops
import NDI_PredicatesBridge
import NDI_PredicatesRef.Funs
import NDI_PredicatesRef.Types
import NDI_RawProjection
import NDI_ReaderByteBridge
import NDI_ReaderByteRef.Funs
import NDI_ReaderByteRef.Types
import NDI_ReaderByteValue
import NDI_ReaderCohort
import NDI_ReaderDomains
import NDI_TranscriptBorrow.Funs
import NDI_TranscriptBorrow.Types
import NDI_TranscriptBridge
import NDI_TranscriptCaller
import NDI_TranscriptInit
import NDI_TranscriptLaw
import NDI_TranscriptRef.Funs
import NDI_TranscriptRef.Types
import NDI_TranscriptWindows

#print axioms NDI_BatchBridge.reference
#print axioms NDI_BatchCaller.canonical
#print axioms NDI_BatchControl.active
#print axioms NDI_BatchControl.done
#print axioms NDI_BatchControl.initial
#print axioms NDI_BatchControl.reached
#print axioms NDI_BatchInstalled.installed
#print axioms NDI_BatchRun.frame_all
#print axioms NDI_BatchRun.run
#print axioms NDI_BatchStep.done_step
#print axioms NDI_BatchStep.frame
#print axioms NDI_BatchStep.step
#print axioms NDI_BatchWord.word
#print axioms NDI_BorrowBridge.initial
#print axioms NDI_BorrowBridge.sample
#print axioms NDI_GeometryBridge.caller
#print axioms NDI_GeometryBridge.reference
#print axioms NDI_HeaderShifts.byte16
#print axioms NDI_HeaderShifts.byte24
#print axioms NDI_HeaderShifts.byte8
#print axioms NDI_IteratorFrame.next_remainder
#print axioms NDI_IteratorFrame.query_prefix
#print axioms NDI_IteratorFrame.remainder
#print axioms NDI_IteratorFrame.selected
#print axioms NDI_IteratorFrame.shape_tail
#print axioms NDI_ParseShapeTail.window
#print axioms NDI_ParseShapeTail.zeros
#print axioms NDI_ParserAt.reference
#print axioms NDI_ParserBody.reference
#print axioms NDI_ParserHeader.reference_eq
#print axioms NDI_ParserInvalid.reference
#print axioms NDI_ParserPayload.cap
#print axioms NDI_ParserPayload.range
#print axioms NDI_ParserPayload.validator
#print axioms NDI_ParserTotal.reference
#print axioms NDI_PredicateLoops.contains
#print axioms NDI_PredicateLoops.emitted_contains
#print axioms NDI_PredicateLoops.pure_any
#print axioms NDI_PredicateLoops.tail
#print axioms NDI_PredicatesBridge.contains
#print axioms NDI_PredicatesBridge.iterator_active
#print axioms NDI_PredicatesBridge.iterator_done
#print axioms NDI_PredicatesBridge.tail
#print axioms NDI_PredicatesBridge.window
#print axioms NDI_RawProjection.byte
#print axioms NDI_RawProjection.kmx_disjoint
#print axioms NDI_RawProjection.kmx_window
#print axioms NDI_ReaderByteBridge.reference
#print axioms NDI_ReaderByteValue.total
#print axioms NDI_ReaderCohort.selected_byte
#print axioms NDI_ReaderDomains.end_position
#print axioms NDI_ReaderDomains.native_fit
#print axioms NDI_ReaderDomains.queries
#print axioms NDI_ReaderDomains.semantic_alpha
#print axioms NDI_ReaderDomains.structural
#print axioms NDI_ReaderDomains.weights
#print axioms NDI_TranscriptBridge.initial
#print axioms NDI_TranscriptBridge.sample
#print axioms NDI_TranscriptCaller.initialized_public
#print axioms NDI_TranscriptInit.length_conversion
#print axioms NDI_TranscriptInit.reference
#print axioms NDI_TranscriptLaw.rejected
#print axioms NDI_TranscriptLaw.sample
#print axioms NDI_TranscriptLaw.sample_domain
#print axioms NDI_TranscriptWindows.complete
#print axioms NDI_TranscriptWindows.initial
#print axioms NDI_TranscriptWindows.sample
