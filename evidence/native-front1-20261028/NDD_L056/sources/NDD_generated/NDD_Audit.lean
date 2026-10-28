import NDD_Reference.Types
import NDD_Reference.Funs
import NDD_Reduce
import NDD_Simple
import NDD_Composite
import NDD_ResultLaws
import NDD_Prepared
import NDD_ChannelPrimitives
import NDD_Channels
import NDD_CopyFrame
import NDD_PackModel
import NDD_SelectorModel
import NDD_LeafRefs
import NDD_BoxModel
import NDD_GuardModel
import NDD_WellformedModel
import NDD_ScalarCanon
import NDD_ReferenceLinear
import NDD_DoubleModel
import NDD_PackPrefix
import NDD_PackSealed
import NDD_TupleContinuation
import NDD_PackArithmetic
import NDD_PackComposition
#print axioms NDD_Reduce.reduce_reference
#print axioms NDD_Reduce.reduce_cohort
#print axioms NDD_Simple.m31_neg
#print axioms NDD_Simple.cm31_from
#print axioms NDD_Composite.cm31_neg
#print axioms NDD_Composite.qm31_zero
#print axioms NDD_ResultLaws.bind_return
#print axioms NDD_Prepared.add_reference
#print axioms NDD_Prepared.prepared
#print axioms NDD_ChannelPrimitives.add
#print axioms NDD_ChannelPrimitives.sub
#print axioms NDD_ChannelPrimitives.reduce
#print axioms NDD_ChannelPrimitives.reconstruct
#print axioms NDD_Channels.cadd
#print axioms NDD_Channels.csub
#print axioms NDD_Channels.byr
#print axioms NDD_Channels.channels
#print axioms NDD_CopyFrame.one_step
#print axioms NDD_CopyFrame.padded_prefix
#print axioms NDD_CopyFrame.disjoint_compose
#print axioms NDD_PackModel.source_cut
#print axioms NDD_PackModel.reference_tail
#print axioms NDD_SelectorModel.field_cut
#print axioms NDD_LeafRefs.arity_bits
#print axioms NDD_LeafRefs.index
#print axioms NDD_LeafRefs.value
#print axioms NDD_LeafRefs.root
#print axioms NDD_BoxModel.parts
#print axioms NDD_GuardModel.cut
#print axioms NDD_WellformedModel.allM_total
#print axioms NDD_WellformedModel.native_step_reference
#print axioms NDD_ScalarCanon.checked_add
#print axioms NDD_ScalarCanon.checked_sub
#print axioms NDD_ReferenceLinear.add
#print axioms NDD_ReferenceLinear.sub
#print axioms NDD_ReferenceLinear.add_canonical
#print axioms NDD_DoubleModel.observed
#print axioms NDD_PackPrefix.bind_prefix
#print axioms NDD_PackPrefix.source_prefix
#print axioms NDD_PackSealed.concrete_source
#print axioms NDD_TupleContinuation.curry_uncurry
#print axioms NDD_TupleContinuation.bind_tuple
#print axioms NDD_PackArithmetic.arithmetic
#print axioms NDD_PackArithmetic.tuple_beta
#print axioms NDD_PackComposition.source_reference
