import NKN_COMBINED_IMPORT
import NKQ_AlphaDomain
import NKQ_ArrayWindows
import NKQ_CanonicalBridge
import NKQ_CircleDomains
import NKQ_ClaimsDomain
import NKQ_ClaimsMatrix
import NKQ_DecodeCanonical
import NKQ_FinishMaskDomain
import NKQ_FinishSlots
import NKQ_FinishStages
import NKQ_FromFnIndices
import NKQ_GetterRepeat
import NKQ_MaskArrays
import NKQ_MaskCanonical
import NKQ_MaskCuts
import NKQ_MaskHighStep
import NKQ_MaskLowStep
import NKQ_ObservedContinuations
import NKQ_ObservedStages
import NKQ_ObservedTrace
import NKQ_PrepareBuffer
import NKQ_PrepareStages
import NKQ_ReadTwo
import NKQ_RecordDomains
import NKQ_StrictDecode
import NKQ_Tx1Stages

-- Source support and domains only; no promotion of TX1:136/137/087/094.
#print axioms AspisR1.RPx_Deployed.deployed
#print AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NKQ_AlphaDomain.full
#print AspisR1.NKQ_AlphaDomain.full
#print axioms AspisR1.NKQ_AlphaDomain.source
#print AspisR1.NKQ_AlphaDomain.source
#print axioms AspisR1.NKQ_ArrayWindows.extensional
#print AspisR1.NKQ_ArrayWindows.extensional
#print axioms AspisR1.NKQ_ArrayWindows.fromFnLoop_bounded
#print AspisR1.NKQ_ArrayWindows.fromFnLoop_bounded
#print axioms AspisR1.NKQ_ArrayWindows.read
#print AspisR1.NKQ_ArrayWindows.read
#print axioms AspisR1.NKQ_CanonicalBridge.canonical
#print AspisR1.NKQ_CanonicalBridge.canonical
#print axioms AspisR1.NKQ_CircleDomains.source
#print AspisR1.NKQ_CircleDomains.source
#print axioms AspisR1.NKQ_ClaimsDomain.convert
#print AspisR1.NKQ_ClaimsDomain.convert
#print axioms AspisR1.NKQ_ClaimsDomain.source
#print AspisR1.NKQ_ClaimsDomain.source
#print axioms AspisR1.NKQ_ClaimsMatrix.canonical
#print AspisR1.NKQ_ClaimsMatrix.canonical
#print axioms AspisR1.NKQ_ClaimsMatrix.reference
#print AspisR1.NKQ_ClaimsMatrix.reference
#print axioms AspisR1.NKQ_ClaimsMatrix.rows
#print AspisR1.NKQ_ClaimsMatrix.rows
#print axioms AspisR1.NKQ_DecodeCanonical.main
#print AspisR1.NKQ_DecodeCanonical.main
#print axioms AspisR1.NKQ_DecodeCanonical.parent
#print AspisR1.NKQ_DecodeCanonical.parent
#print axioms AspisR1.NKQ_FinishMaskDomain.source
#print AspisR1.NKQ_FinishMaskDomain.source
#print axioms AspisR1.NKQ_FinishSlots.source
#print AspisR1.NKQ_FinishSlots.source
#print axioms AspisR1.NKQ_FinishStages.claims_error
#print AspisR1.NKQ_FinishStages.claims_error
#print axioms AspisR1.NKQ_FinishStages.factor
#print AspisR1.NKQ_FinishStages.factor
#print axioms AspisR1.NKQ_FinishStages.terminal_error
#print AspisR1.NKQ_FinishStages.terminal_error
#print axioms AspisR1.NKQ_FromFnIndices.bound
#print AspisR1.NKQ_FromFnIndices.bound
#print axioms AspisR1.NKQ_FromFnIndices.length
#print AspisR1.NKQ_FromFnIndices.length
#print axioms AspisR1.NKQ_FromFnIndices.total
#print AspisR1.NKQ_FromFnIndices.total
#print axioms AspisR1.NKQ_GetterRepeat.duplicate
#print AspisR1.NKQ_GetterRepeat.duplicate
#print axioms AspisR1.NKQ_GetterRepeat.source
#print AspisR1.NKQ_GetterRepeat.source
#print axioms AspisR1.NKQ_MaskArrays.high_source
#print AspisR1.NKQ_MaskArrays.high_source
#print axioms AspisR1.NKQ_MaskArrays.low_source
#print AspisR1.NKQ_MaskArrays.low_source
#print axioms AspisR1.NKQ_MaskCanonical.claim_cell
#print AspisR1.NKQ_MaskCanonical.claim_cell
#print axioms AspisR1.NKQ_MaskCanonical.domain
#print AspisR1.NKQ_MaskCanonical.domain
#print axioms AspisR1.NKQ_MaskCanonical.high
#print AspisR1.NKQ_MaskCanonical.high
#print axioms AspisR1.NKQ_MaskCanonical.low
#print AspisR1.NKQ_MaskCanonical.low
#print axioms AspisR1.NKQ_MaskCuts.arguments
#print AspisR1.NKQ_MaskCuts.arguments
#print axioms AspisR1.NKQ_MaskHighStep.step
#print AspisR1.NKQ_MaskHighStep.step
#print axioms AspisR1.NKQ_MaskLowStep.frame
#print AspisR1.NKQ_MaskLowStep.frame
#print axioms AspisR1.NKQ_MaskLowStep.step
#print AspisR1.NKQ_MaskLowStep.step
#print axioms AspisR1.NKQ_ObservedContinuations.begin_error
#print AspisR1.NKQ_ObservedContinuations.begin_error
#print axioms AspisR1.NKQ_ObservedContinuations.finish_same_call
#print AspisR1.NKQ_ObservedContinuations.finish_same_call
#print axioms AspisR1.NKQ_ObservedContinuations.parsed_success
#print AspisR1.NKQ_ObservedContinuations.parsed_success
#print axioms AspisR1.NKQ_ObservedContinuations.public_error
#print AspisR1.NKQ_ObservedContinuations.public_error
#print axioms AspisR1.NKQ_ObservedStages.factor
#print AspisR1.NKQ_ObservedStages.factor
#print axioms AspisR1.NKQ_ObservedStages.parsed_div
#print AspisR1.NKQ_ObservedStages.parsed_div
#print axioms AspisR1.NKQ_ObservedStages.parsed_error
#print AspisR1.NKQ_ObservedStages.parsed_error
#print axioms AspisR1.NKQ_ObservedStages.parsed_fail
#print AspisR1.NKQ_ObservedStages.parsed_fail
#print axioms AspisR1.NKQ_ObservedTrace.factor
#print AspisR1.NKQ_ObservedTrace.factor
#print axioms AspisR1.NKQ_ObservedTrace.parser_rejection
#print AspisR1.NKQ_ObservedTrace.parser_rejection
#print axioms AspisR1.NKQ_PrepareBuffer.buffer_error
#print AspisR1.NKQ_PrepareBuffer.buffer_error
#print axioms AspisR1.NKQ_PrepareBuffer.factor
#print AspisR1.NKQ_PrepareBuffer.factor
#print axioms AspisR1.NKQ_PrepareStages.factor
#print AspisR1.NKQ_PrepareStages.factor
#print axioms AspisR1.NKQ_PrepareStages.semantic_error
#print AspisR1.NKQ_PrepareStages.semantic_error
#print axioms AspisR1.NKQ_ReadTwo.readTwo
#print AspisR1.NKQ_ReadTwo.readTwo
#print axioms AspisR1.NKQ_RecordDomains.entered
#print AspisR1.NKQ_RecordDomains.entered
#print axioms AspisR1.NKQ_StrictDecode.total
#print AspisR1.NKQ_StrictDecode.total
#print axioms AspisR1.NKQ_Tx1Stages.factor
#print AspisR1.NKQ_Tx1Stages.factor
#print axioms AspisR1.NKQ_Tx1Stages.query_error
#print AspisR1.NKQ_Tx1Stages.query_error
#print axioms AspisR1.NKQ_Tx1Stages.writer_frame
#print AspisR1.NKQ_Tx1Stages.writer_frame
