import NDF_Reference.Types
import NDF_Reference.Funs
import NDF_ScalarBridge
import NDF_LeafBridge
import NDF_ScalarInspect
import NDF_CheckedWrapping
import NDF_OpeningBridge
import NDF_BatchDomains
import NDF_ReaderRef.Types
import NDF_ReaderRef.Funs
import NDF_RecordBridge
import NDF_RawStep
import NDF_RawState
import NDF_RawRun
import NDF_RawValue
import NDF_RawBridge
import NDF_ParserDomain
import NDF_AcceptedFrame
#print axioms NDF_ScalarBridge.key
#print axioms NDF_ScalarBridge.same_index
#print axioms NDF_ScalarBridge.row
#print axioms NDF_ScalarBridge.framed
#print axioms NDF_ScalarBridge.state
#print axioms NDF_LeafBridge.same_leaf
#print axioms NDF_CheckedWrapping.mul
#print axioms NDF_CheckedWrapping.add
#print axioms NDF_OpeningBridge.reference
#print axioms NDF_BatchDomains.position
#print axioms NDF_BatchDomains.duplicate
#print axioms NDF_BatchDomains.key_read
#print axioms NDF_BatchDomains.index_read
#print axioms NDF_BatchDomains.opening_exact
#print axioms NDF_RecordBridge.reference
#print axioms NDF_RawStep.step
#print axioms NDF_RawStep.done_step
#print axioms NDF_RawState.initial
#print axioms NDF_RawState.extend
#print axioms NDF_RawState.frame
#print axioms NDF_RawState.complete
#print axioms NDF_RawRun.run
#print axioms NDF_RawValue.total
#print axioms NDF_RawBridge.cohort
#print axioms NDF_ParserDomain.shape_source
#print axioms NDF_ParserDomain.shape_bound
#print axioms NDF_ParserDomain.framed_cap
#print axioms NDF_AcceptedFrame.wrong_length
#print axioms NDF_AcceptedFrame.accepted
