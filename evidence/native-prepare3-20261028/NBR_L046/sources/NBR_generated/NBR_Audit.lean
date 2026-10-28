import NBL_Audit
import KMX_CopyMeaning
import NBR_AppendInduction
import NBR_BlockConstruct
import NBR_BufferJoin
import NBR_ExpansionReturn
import NBR_MaterialConstruct
import NBR_OpeningConstruct
import NBR_OpeningPayload
import NBR_PrepareConstruct
import NBR_PrepareTotal
import NBR_PreparedFields
import NBR_ProducerBuffers
import NBR_QueryConstruct
import NBR_QueryOutcome
import NBR_QueryTotal
import NBR_RangeGeometry
import NBR_RangeJoin
import NBR_ReturnedInputs
import NBR_SemanticFinish
import NBR_SemanticGeometry
import NBR_SemanticReturn
import NBR_SemanticStep
import NBR_ValuesPort
import NBR_VecAppend

-- Audit the accepted current roots after the focused dependent builds.
#print axioms AspisR1.NBR_AppendInduction.step
#print axioms AspisR1.NBR_AppendInduction.prefix_step
#print axioms AspisR1.NBR_AppendInduction.capacity
#print axioms AspisR1.NBR_BlockConstruct.block
#print axioms AspisR1.NBR_BlockConstruct.scalar
#print axioms AspisR1.NBR_BlockConstruct.returned
#print axioms AspisR1.NBR_BufferJoin.source
#print axioms AspisR1.NBR_ExpansionReturn.source
#print axioms AspisR1.NBR_ExpansionReturn.no_error
#print axioms AspisR1.NBR_MaterialConstruct.pair
#print axioms AspisR1.NBR_MaterialConstruct.source
#print axioms AspisR1.NBR_OpeningConstruct.source
#print axioms AspisR1.NBR_OpeningPayload.source
#print axioms AspisR1.NBR_OpeningPayload.push_bound
#print axioms AspisR1.NBR_PrepareConstruct.source
#print axioms AspisR1.NBR_PrepareTotal.source
#print axioms AspisR1.NBR_PreparedFields.source
#print axioms AspisR1.NBR_ProducerBuffers.source
#print axioms AspisR1.NBR_QueryConstruct.initial
#print axioms AspisR1.NBR_QueryConstruct.source
#print axioms AspisR1.NBR_QueryOutcome.source
#print axioms AspisR1.NBR_QueryTotal.finish
#print axioms AspisR1.NBR_QueryTotal.walk
#print axioms AspisR1.NBR_RangeGeometry.difference
#print axioms AspisR1.NBR_RangeGeometry.length
#print axioms AspisR1.NBR_RangeJoin.first
#print axioms AspisR1.NBR_RangeJoin.suffix
#print axioms AspisR1.NBR_ReturnedInputs.source
#print axioms AspisR1.NBR_SemanticFinish.source
#print axioms AspisR1.NBR_SemanticGeometry.source
#print axioms AspisR1.NBR_SemanticReturn.source
#print axioms AspisR1.NBR_SemanticReturn.returned
#print axioms AspisR1.NBR_SemanticStep.source
#print axioms AspisR1.NBR_ValuesPort.construct
#print axioms AspisR1.NBR_ValuesPort.returned
#print axioms AspisR1.NBR_VecAppend.total
#print axioms AspisR1.NBR_VecAppend.clone_list
#print axioms AspisR1.NBR_VecAppend.clone_slice
#print axioms AspisR1.NBR_VecAppend.extend
