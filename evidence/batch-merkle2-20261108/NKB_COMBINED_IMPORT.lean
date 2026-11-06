import NJW_COMBINED_IMPORT
import NJS_COMBINED_IMPORT
import NJV_COMBINED_IMPORT
import NKB_Rejection
import NKB_IndexFold
import NKB_CallerDomain
import NKB_CallerPrefix
import NKB_DedupCut
import NKB_LeafChain
import NKB_PaddingFrame
import NKB_PaddingPredicate
import NKB_ScanWindows
import NKB_SortProducer
import NKB_StrictCount
import NKB_StrictLeaves
import NKB_DomainFinding
import NKB_ProducerChain
import NKB_AnyModel
import NKB_KeyStream
import NKB_ParseCut

set_option pp.proofs false
#print AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.RPx_Deployed.deployed
#print NKB_Rejection.lost_error
#print axioms NKB_Rejection.lost_error
#print NKB_Rejection.count_none
#print axioms NKB_Rejection.count_none
#print NKB_IndexFold.insert_bounds
#print axioms NKB_IndexFold.insert_bounds
#print NKB_IndexFold.build_bounds
#print axioms NKB_IndexFold.build_bounds
#print NKB_IndexFold.build_positive
#print axioms NKB_IndexFold.build_positive
#print NKB_IndexFold.build_upper
#print axioms NKB_IndexFold.build_upper
#print NKB_IndexFold.producer
#print axioms NKB_IndexFold.producer
#print NKB_CallerDomain.well
#print axioms NKB_CallerDomain.well
#print NKB_CallerPrefix.counted
#print axioms NKB_CallerPrefix.counted
#print NKB_CallerPrefix.bytes
#print axioms NKB_CallerPrefix.bytes
#print NKB_DedupCut.source
#print axioms NKB_DedupCut.source
#print NKB_DedupCut.cursor
#print axioms NKB_DedupCut.cursor
#print NKB_LeafChain.source
#print axioms NKB_LeafChain.source
#print NKB_LeafChain.cursor
#print axioms NKB_LeafChain.cursor
#print NKB_PaddingFrame.aligned
#print axioms NKB_PaddingFrame.aligned
#print NKB_PaddingFrame.zero_suffix
#print axioms NKB_PaddingFrame.zero_suffix
#print NKB_PaddingFrame.nonzero_rejects
#print axioms NKB_PaddingFrame.nonzero_rejects
#print NKB_PaddingPredicate.source
#print axioms NKB_PaddingPredicate.source
#print NKB_PaddingPredicate.zero_iff
#print axioms NKB_PaddingPredicate.zero_iff
#print NKB_PaddingPredicate.first_nonzero
#print axioms NKB_PaddingPredicate.first_nonzero
#print NKB_ScanWindows.offsets
#print axioms NKB_ScanWindows.offsets
#print NKB_ScanWindows.subdomain
#print axioms NKB_ScanWindows.subdomain
#print NKB_SortProducer.sorted
#print axioms NKB_SortProducer.sorted
#print NKB_SortProducer.tx2_keys
#print axioms NKB_SortProducer.tx2_keys
#print NKB_SortProducer.tx1_keys
#print axioms NKB_SortProducer.tx1_keys
#print NKB_StrictCount.build_count
#print axioms NKB_StrictCount.build_count
#print NKB_StrictCount.ordered
#print axioms NKB_StrictCount.ordered
#print NKB_StrictCount.canonical
#print axioms NKB_StrictCount.canonical
#print NKB_StrictCount.twelve
#print axioms NKB_StrictCount.twelve
#print NKB_StrictCount.not_ten
#print axioms NKB_StrictCount.not_ten
#print NKB_StrictLeaves.total
#print axioms NKB_StrictLeaves.total
#print NKB_StrictLeaves.twelve
#print axioms NKB_StrictLeaves.twelve
#print NKB_DomainFinding.indices
#print axioms NKB_DomainFinding.indices
#print NKB_DomainFinding.unit_counterexample
#print axioms NKB_DomainFinding.unit_counterexample
#print NKB_ProducerChain.caller
#print axioms NKB_ProducerChain.caller
#print NKB_ProducerChain.verifier_bytes
#print axioms NKB_ProducerChain.verifier_bytes
#print NKB_AnyModel.callback
#print axioms NKB_AnyModel.callback
#print NKB_AnyModel.total
#print axioms NKB_AnyModel.total
#print NKB_AnyModel.predicate_false
#print axioms NKB_AnyModel.predicate_false
#print NKB_AnyModel.false_iff
#print axioms NKB_AnyModel.false_iff
#print NKB_KeyStream.positive
#print axioms NKB_KeyStream.positive
#print NKB_KeyStream.built
#print axioms NKB_KeyStream.built
#print NKB_KeyStream.initial
#print axioms NKB_KeyStream.initial
#print NKB_KeyStream.source
#print axioms NKB_KeyStream.source
#print NKB_ParseCut.mismatch
#print axioms NKB_ParseCut.mismatch
