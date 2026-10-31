import NEB_ActualGeometryLine
import NEB_ActualGeometryModel
import NEB_ActualGeometryPoint
import NEB_AdditiveCalls
import NEB_AdditiveComposed
import NEB_AdditiveFrames
import NEB_AdditiveRef.Funs
import NEB_AdditiveRef.Types
import NEB_ArrayRefs
import NEB_BaseCallBounds
import NEB_ByRCalls
import NEB_CMCalls
import NEB_CMCarrier
import NEB_CheckedScalar
import NEB_EmbeddingDomain
import NEB_FieldDomains
import NEB_FieldFrames
import NEB_GeometryAccessor
import NEB_GeometryBoundary
import NEB_GeometryDictionaryEq
import NEB_GeometryFieldPorts
import NEB_GeometryGatherDomains
import NEB_GeometryIndices
import NEB_GeometryModel
import NEB_GeometryPrimitives
import NEB_InstalledOpening
import NEB_InverseCalls
import NEB_LineCalls
import NEB_MulReducerCall
import NEB_NativeFieldScalars
import NEB_PointCalls
import NEB_PointSuccess
import NEB_PrivateReducer
import NEB_PureFrame
import NEB_QMCalls
import NEB_QueryCallRanges
import NEB_QueryNodeDomains
import NEB_ReducerCall
import NEB_Reference.Funs
import NEB_Reference.Types
import NEB_RepresentationRef.Funs
import NEB_RepresentationRef.Types
import NEB_RepresentationRefs
import NEB_SquareComposition
import NEB_SquareDomains
import NEB_TableCalls
import NEB_TraceFrame
import NEB_WideCalls
import NEB_WideRepresentation
import NEB_WideSubCalls
import NEB_WideSubRef
import NEB_WordRefs
set_option autoImplicit false
#print axioms NEB_ActualGeometryLine.calls
#print axioms NEB_ActualGeometryModel.for_range
#print axioms NEB_ActualGeometryModel.primitives
#print axioms NEB_ActualGeometryModel.same_dictionary
#print axioms NEB_ActualGeometryPoint.calls
#print axioms NEB_ActualGeometryPoint.frame
#print axioms NEB_AdditiveCalls.base_double_arguments
#print axioms NEB_AdditiveCalls.double_arguments
#print axioms NEB_AdditiveCalls.qm_scale
#print axioms NEB_AdditiveCalls.wide_add
#print axioms NEB_AdditiveComposed.cm_add
#print axioms NEB_AdditiveComposed.cm_double
#print axioms NEB_AdditiveComposed.cm_sub
#print axioms NEB_AdditiveComposed.m_add
#print axioms NEB_AdditiveComposed.m_double
#print axioms NEB_AdditiveComposed.m_sub
#print axioms NEB_AdditiveComposed.qm_add
#print axioms NEB_AdditiveComposed.qm_sub
#print axioms NEB_AdditiveComposed.wide_add
#print axioms NEB_AdditiveFrames.cm_add
#print axioms NEB_AdditiveFrames.cm_double
#print axioms NEB_AdditiveFrames.cm_sub
#print axioms NEB_AdditiveFrames.m_add
#print axioms NEB_AdditiveFrames.m_double
#print axioms NEB_AdditiveFrames.m_sub
#print axioms NEB_AdditiveFrames.qm_add
#print axioms NEB_AdditiveFrames.qm_sub
#print axioms NEB_AdditiveFrames.wide_add
#print axioms NEB_AdditiveFrames.wide_sub
#print axioms NEB_ArrayRefs.cm_add
#print axioms NEB_ArrayRefs.cm_injective
#print axioms NEB_ArrayRefs.cm_sub
#print axioms NEB_ArrayRefs.qm_add
#print axioms NEB_ArrayRefs.qm_injective
#print axioms NEB_ArrayRefs.qm_sub
#print axioms NEB_ArrayRefs.wide_add
#print axioms NEB_ArrayRefs.wide_injective
#print axioms NEB_BaseCallBounds.add
#print axioms NEB_BaseCallBounds.multiply_reducer
#print axioms NEB_BaseCallBounds.raw_product
#print axioms NEB_BaseCallBounds.reducer
#print axioms NEB_BaseCallBounds.reducer_wrapper
#print axioms NEB_BaseCallBounds.sub
#print axioms NEB_ByRCalls.mul_u
#print axioms NEB_ByRCalls.source
#print axioms NEB_CMCalls.multiply
#print axioms NEB_CMCalls.scale
#print axioms NEB_CMCarrier.actual_casts
#print axioms NEB_CMCarrier.lossless
#print axioms NEB_CheckedScalar.accepted
#print axioms NEB_CheckedScalar.push_arguments
#print axioms NEB_CheckedScalar.value_arguments
#print axioms NEB_EmbeddingDomain.canonical_edge
#print axioms NEB_EmbeddingDomain.canonical_output
#print axioms NEB_FieldDomains.cm_add_calls
#print axioms NEB_FieldDomains.cm_arguments
#print axioms NEB_FieldDomains.cm_cross_arguments
#print axioms NEB_FieldDomains.cm_sub_calls
#print axioms NEB_FieldDomains.qm_arguments
#print axioms NEB_FieldDomains.wide_arguments
#print axioms NEB_FieldFrames.by_r
#print axioms NEB_FieldFrames.cm_mul
#print axioms NEB_FieldFrames.cm_scale
#print axioms NEB_FieldFrames.mul_u
#print axioms NEB_FieldFrames.qm_mul
#print axioms NEB_FieldFrames.qm_scale
#print axioms NEB_FieldFrames.wide_mixed
#print axioms NEB_FieldFrames.wide_mul
#print axioms NEB_FieldFrames.wide_scale
#print axioms NEB_GeometryAccessor.caller
#print axioms NEB_GeometryAccessor.result
#print axioms NEB_GeometryBoundary.empty_terminal
#print axioms NEB_GeometryBoundary.invalid_end
#print axioms NEB_GeometryBoundary.invalid_start
#print axioms NEB_GeometryDictionaryEq.line
#print axioms NEB_GeometryDictionaryEq.line_success
#print axioms NEB_GeometryDictionaryEq.point
#print axioms NEB_GeometryDictionaryEq.point_success
#print axioms NEB_GeometryFieldPorts.add
#print axioms NEB_GeometryFieldPorts.cm_eq
#print axioms NEB_GeometryFieldPorts.double
#print axioms NEB_GeometryFieldPorts.physical
#print axioms NEB_GeometryFieldPorts.sub
#print axioms NEB_GeometryGatherDomains.step
#print axioms NEB_GeometryGatherDomains.traversal
#print axioms NEB_GeometryIndices.accepted
#print axioms NEB_GeometryIndices.admitted
#print axioms NEB_GeometryIndices.aligned
#print axioms NEB_GeometryIndices.primitives
#print axioms NEB_GeometryModel.for_range
#print axioms NEB_GeometryModel.primitives
#print axioms NEB_GeometryPrimitives.primitives
#print axioms NEB_InstalledOpening.accepted_query
#print axioms NEB_InstalledOpening.same_return
#print axioms NEB_InverseCalls.nonzero
#print axioms NEB_InverseCalls.zero
#print axioms NEB_LineCalls.admitted
#print axioms NEB_LineCalls.successful
#print axioms NEB_MulReducerCall.callsite
#print axioms NEB_MulReducerCall.domain
#print axioms NEB_MulReducerCall.input_value
#print axioms NEB_MulReducerCall.state_effects
#print axioms NEB_MulReducerCall.value
#print axioms NEB_NativeFieldScalars.cross_checked
#print axioms NEB_NativeFieldScalars.m31_checked_product
#print axioms NEB_NativeFieldScalars.size64
#print axioms NEB_NativeFieldScalars.sum_checked
#print axioms NEB_PointCalls.canonical_point
#print axioms NEB_PointCalls.selected_product
#print axioms NEB_PointCalls.state_effects
#print axioms NEB_PointSuccess.canonical
#print axioms NEB_PointSuccess.read_bound
#print axioms NEB_PrivateReducer.constant_cast
#print axioms NEB_PrivateReducer.frame
#print axioms NEB_PrivateReducer.reference
#print axioms NEB_PureFrame.equality
#print axioms NEB_PureFrame.successful
#print axioms NEB_QMCalls.add
#print axioms NEB_QMCalls.multiply
#print axioms NEB_QMCalls.sub
#print axioms NEB_QueryCallRanges.calls
#print axioms NEB_QueryCallRanges.root
#print axioms NEB_QueryNodeDomains.accepted
#print axioms NEB_QueryNodeDomains.reached
#print axioms NEB_ReducerCall.all_domain
#print axioms NEB_ReducerCall.reference
#print axioms NEB_ReducerCall.state_effects
#print axioms NEB_ReducerCall.value
#print axioms NEB_ReducerCall.wrapper
#print axioms NEB_RepresentationRefs.canonical
#print axioms NEB_RepresentationRefs.canonical_frame
#print axioms NEB_RepresentationRefs.e_injective
#print axioms NEB_RepresentationRefs.e_roundtrip
#print axioms NEB_RepresentationRefs.embedding
#print axioms NEB_RepresentationRefs.embedding_frame
#print axioms NEB_RepresentationRefs.embedding_injective
#print axioms NEB_RepresentationRefs.embedding_roundtrip
#print axioms NEB_RepresentationRefs.getter
#print axioms NEB_RepresentationRefs.getter_frame
#print axioms NEB_RepresentationRefs.q_injective
#print axioms NEB_RepresentationRefs.q_roundtrip
#print axioms NEB_SquareComposition.cell
#print axioms NEB_SquareComposition.loop_frame
#print axioms NEB_SquareComposition.trace_frame
#print axioms NEB_SquareDomains.positive
#print axioms NEB_SquareDomains.preserve
#print axioms NEB_SquareDomains.source
#print axioms NEB_SquareDomains.trace_exists
#print axioms NEB_TableCalls.constructor
#print axioms NEB_TableCalls.constructor_frame
#print axioms NEB_TableCalls.getter_frame
#print axioms NEB_TableCalls.selected_table
#print axioms NEB_TableCalls.table_body
#print axioms NEB_TableCalls.table_frame
#print axioms NEB_TraceFrame.result
#print axioms NEB_WideCalls.mixed
#print axioms NEB_WideCalls.multiply
#print axioms NEB_WideCalls.scale
#print axioms NEB_WideRepresentation.canonical
#print axioms NEB_WideRepresentation.canonical_calls
#print axioms NEB_WideRepresentation.canonical_frame
#print axioms NEB_WideRepresentation.embedding_call
#print axioms NEB_WideRepresentation.embedding_frame
#print axioms NEB_WideRepresentation.limbs_frame
#print axioms NEB_WideRepresentation.word
#print axioms NEB_WideSubCalls.source
#print axioms NEB_WideSubRef.reference
#print axioms NEB_WideSubRef.result
#print axioms NEB_WordRefs.add
#print axioms NEB_WordRefs.double
#print axioms NEB_WordRefs.normalize
#print axioms NEB_WordRefs.normalize_value
#print axioms NEB_WordRefs.sub
