import NBF_Audit
import NBO_AcceptedTail
import NBO_AccumulateAssociation
import NBO_AllCalls
import NBO_CircleDomain
import NBO_Composite
import NBO_Entry
import NBO_Enumerate
import NBO_EveryCaller
import NBO_FieldPorts
import NBO_FieldSemantics
import NBO_FinishCaller
import NBO_FoldLinear
import NBO_GeometryDomain
import NBO_LoopAssociation
import NBO_ProducerDomains
import NBO_QueryAssociation
import NBO_QueryDomains
import NBO_QueryFactor
import NBO_QueryRhs
import NBO_Release
import NBO_SquareCut
import NBO_TailDomain
import NBO_TopInstall
import NBO_WeightRead
import NBO_WriterEntry

#print axioms NBO_AcceptedTail.reached
#print axioms NBO_AcceptedTail.canonical
#print axioms NBO_AccumulateAssociation.prefix_terms
#print axioms NBO_AccumulateAssociation.source
#print axioms NBO_AllCalls.initial_weights
#print axioms NBO_AllCalls.reached
#print axioms NBO_CircleDomain.reached
#print axioms NBO_Composite.association
#print axioms NBO_Composite.accepted
#print axioms NBO_Entry.domains
#print axioms NBO_Entry.association
#print axioms NBO_Enumerate.from_cursor
#print axioms NBO_EveryCaller.ready
#print axioms NBO_FieldPorts.q_roundtrip
#print axioms NBO_FieldPorts.e_roundtrip
#print axioms NBO_FieldPorts.probe_q_roundtrip
#print axioms NBO_FieldPorts.probe_e_roundtrip
#print axioms NBO_FieldPorts.canonicalQ
#print axioms NBO_FieldPorts.canonicalE
#print axioms NBO_FieldPorts.fromQ_canonical
#print axioms NBO_FieldPorts.fromE_canonical
#print axioms NBO_FieldSemantics.add_total
#print axioms NBO_FieldSemantics.product_total
#print axioms NBO_FieldSemantics.power_total
#print axioms NBO_FieldSemantics.fields
#print axioms NBO_FinishCaller.from_query
#print axioms NBO_FoldLinear.qsub_total
#print axioms NBO_FoldLinear.sub_total
#print axioms NBO_FoldLinear.scale_total
#print axioms NBO_GeometryDomain.node_input
#print axioms NBO_LoopAssociation.transport
#print axioms NBO_LoopAssociation.from_constructors
#print axioms NBO_ProducerDomains.top
#print axioms NBO_QueryAssociation.source
#print axioms NBO_QueryDomains.closure
#print axioms NBO_QueryDomains.front
#print axioms NBO_QueryFactor.association
#print axioms NBO_QueryRhs.trace
#print axioms NBO_QueryRhs.from_constructors
#print axioms NBO_Release.lower
#print axioms NBO_Release.fields
#print axioms NBO_Release.mark_none
#print axioms NBO_SquareCut.association
#print axioms NBO_TailDomain.initial
#print axioms NBO_TailDomain.accumulate
#print axioms NBO_TopInstall.reached
#print axioms NBO_WeightRead.read
#print axioms NBO_WeightRead.embed
#print axioms NBO_WriterEntry.same_writer
#check NBO_QueryAssociation.source
#check NBO_AccumulateAssociation.source
#check NBO_Entry.association
#check NBO_WriterEntry.same_writer
#check NBO_QueryDomains.Lower
#check NBO_FieldSemantics.NBC_Bindings
#check NBO_ProducerDomains.NBA_NBC
#check NBO_Entry.NBC_Bounds
