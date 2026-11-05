import NGK_COMBINED_IMPORT
import NID_COMBINED_IMPORT
import NIL_Carriers
import NIL_StatePort
import NIL_ResultTransport
import NIL_ResultReverse
import NIL_FreshOps
import NIL_SectionPorts
import NIL_HeaderAny
import NIL_TryTransport
import NIL_AllocationPort
import NIL_ResumePrefixCut
import NIL_CursorSub
import NIL_ResumeTailCut
import NIL_MerkleStep
import NIL_QueryPending
import NIL_WindowLayout
import NIL_ReadOutput
import NIL_ResultCases
import NIL_ResumePrefixPort
import NIL_SpineCongr
import NIL_ResumeCohortTail
import NIL_ResumeSplit
import NIL_CohortSplit
import NIL_PortBind
import NIL_ResumeComposition
import NIL_ReplyCases
import NIL_HistoryWindows

#check NIL_Carriers.k_roundtrip
#print axioms NIL_Carriers.k_roundtrip
#check NIL_Carriers.k_reverse
#print axioms NIL_Carriers.k_reverse
#check NIL_Carriers.e_roundtrip
#print axioms NIL_Carriers.e_roundtrip
#check NIL_Carriers.e_reverse
#print axioms NIL_Carriers.e_reverse
#check NIL_Carriers.reader_roundtrip
#print axioms NIL_Carriers.reader_roundtrip
#check NIL_Carriers.reader_reverse
#print axioms NIL_Carriers.reader_reverse
#check NIL_Carriers.variant_roundtrip
#print axioms NIL_Carriers.variant_roundtrip
#check NIL_Carriers.error_roundtrip
#print axioms NIL_Carriers.error_roundtrip
#check NIL_Carriers.error_reverse
#print axioms NIL_Carriers.error_reverse
#check NIL_StatePort.point_roundtrip
#print axioms NIL_StatePort.point_roundtrip
#check NIL_StatePort.point_reverse
#print axioms NIL_StatePort.point_reverse
#check NIL_StatePort.variant_reverse
#print axioms NIL_StatePort.variant_reverse
#check NIL_StatePort.prepared_roundtrip
#print axioms NIL_StatePort.prepared_roundtrip
#check NIL_StatePort.prepared_reverse
#print axioms NIL_StatePort.prepared_reverse
#check NIL_StatePort.accumulator_roundtrip
#print axioms NIL_StatePort.accumulator_roundtrip
#check NIL_StatePort.accumulator_reverse
#print axioms NIL_StatePort.accumulator_reverse
#check NIL_StatePort.pair_roundtrip
#print axioms NIL_StatePort.pair_roundtrip
#check NIL_StatePort.pair_injective
#print axioms NIL_StatePort.pair_injective
#check NIL_StatePort.reply_injective
#print axioms NIL_StatePort.reply_injective
#check NIL_ResultTransport.outer_bind
#print axioms NIL_ResultTransport.outer_bind
#check NIL_ResultTransport.outer_comp
#print axioms NIL_ResultTransport.outer_comp
#check NIL_ResultTransport.outer_roundtrip
#print axioms NIL_ResultTransport.outer_roundtrip
#check NIL_ResultTransport.inner_roundtrip
#print axioms NIL_ResultTransport.inner_roundtrip
#check NIL_ResultTransport.outer_injective
#print axioms NIL_ResultTransport.outer_injective
#check NIL_ResultTransport.inner_injective
#print axioms NIL_ResultTransport.inner_injective
#check NIL_ResultTransport.outer_ok_iff
#print axioms NIL_ResultTransport.outer_ok_iff
#check NIL_ResultTransport.array_comp
#print axioms NIL_ResultTransport.array_comp
#check NIL_ResultTransport.array_roundtrip
#print axioms NIL_ResultTransport.array_roundtrip
#check NIL_ResultTransport.vec_roundtrip
#print axioms NIL_ResultTransport.vec_roundtrip
#check NIL_ResultReverse.inner_reverse
#print axioms NIL_ResultReverse.inner_reverse
#check NIL_ResultReverse.bind_outer
#print axioms NIL_ResultReverse.bind_outer
#check NIL_ResultReverse.outer_if
#print axioms NIL_ResultReverse.outer_if
#check NIL_ResultReverse.outer_fail_iff
#print axioms NIL_ResultReverse.outer_fail_iff
#check NIL_ResultReverse.outer_div_iff
#print axioms NIL_ResultReverse.outer_div_iff
#check NIL_FreshOps.raw_port
#print axioms NIL_FreshOps.raw_port
#check NIL_FreshOps.k_port
#print axioms NIL_FreshOps.k_port
#check NIL_FreshOps.e_port
#print axioms NIL_FreshOps.e_port
#check NIL_SectionPorts.semantic
#print axioms NIL_SectionPorts.semantic
#check NIL_SectionPorts.weights
#print axioms NIL_SectionPorts.weights
#check NIL_SectionPorts.validation
#print axioms NIL_SectionPorts.validation
#check NIL_HeaderAny.loop
#print axioms NIL_HeaderAny.loop
#check NIL_HeaderAny.source
#print axioms NIL_HeaderAny.source
#check NIL_TryTransport.map_try
#print axioms NIL_TryTransport.map_try
#check NIL_TryTransport.fresh_err
#print axioms NIL_TryTransport.fresh_err
#check NIL_TryTransport.fresh_ok
#print axioms NIL_TryTransport.fresh_ok
#check NIL_AllocationPort.source
#print axioms NIL_AllocationPort.source
#check NIL_CursorSub.value
#print axioms NIL_CursorSub.value
#check NIL_CursorSub.source
#print axioms NIL_CursorSub.source
#check NIL_MerkleStep.selected
#print axioms NIL_MerkleStep.selected
#check NIL_QueryPending.source
#print axioms NIL_QueryPending.source
#check NIL_QueryPending.width
#print axioms NIL_QueryPending.width
#check NIL_QueryPending.copied
#print axioms NIL_QueryPending.copied
#check NIL_QueryPending.frame
#print axioms NIL_QueryPending.frame
#check NIL_QueryPending.kmx
#print axioms NIL_QueryPending.kmx
#check NIL_WindowLayout.block
#print axioms NIL_WindowLayout.block
#check NIL_WindowLayout.round0
#print axioms NIL_WindowLayout.round0
#check NIL_WindowLayout.round1
#print axioms NIL_WindowLayout.round1
#check NIL_WindowLayout.final
#print axioms NIL_WindowLayout.final
#check NIL_WindowLayout.scan_final
#print axioms NIL_WindowLayout.scan_final
#check NIL_ReadOutput.k
#print axioms NIL_ReadOutput.k
#check NIL_ReadOutput.e
#print axioms NIL_ReadOutput.e
#check NIL_ResultCases.outer_ok
#print axioms NIL_ResultCases.outer_ok
#check NIL_ResultCases.outer_fail
#print axioms NIL_ResultCases.outer_fail
#check NIL_ResultCases.outer_div
#print axioms NIL_ResultCases.outer_div
#check NIL_ResultCases.inner_ok
#print axioms NIL_ResultCases.inner_ok
#check NIL_ResultCases.inner_err
#print axioms NIL_ResultCases.inner_err
#check NIL_ResultCases.outer_ite
#print axioms NIL_ResultCases.outer_ite
#check NIL_ResultCases.outer_prodlet
#print axioms NIL_ResultCases.outer_prodlet
#check NIL_ResultCases.bind_congr
#print axioms NIL_ResultCases.bind_congr
#check NIL_ResultCases.branch_congr
#print axioms NIL_ResultCases.branch_congr
#check NIL_ResultCases.map_match
#print axioms NIL_ResultCases.map_match
#check NIL_ResultCases.match_congr
#print axioms NIL_ResultCases.match_congr
#check NIL_ResultCases.map_bind_congr
#print axioms NIL_ResultCases.map_bind_congr
#check NIL_ResultCases.checkpoint_error
#print axioms NIL_ResultCases.checkpoint_error
#check NIL_ResumePrefixPort.source
#print axioms NIL_ResumePrefixPort.source
#check NIL_SpineCongr.prod
#print axioms NIL_SpineCongr.prod
#check NIL_ResumeSplit.source
#print axioms NIL_ResumeSplit.source
#check NIL_CohortSplit.source
#print axioms NIL_CohortSplit.source
#check NIL_PortBind.source
#print axioms NIL_PortBind.source
#check NIL_PortBind.read
#print axioms NIL_PortBind.read
#check NIL_ResumeComposition.source
#print axioms NIL_ResumeComposition.source
#check NIL_ReplyCases.ok_iff
#print axioms NIL_ReplyCases.ok_iff
#check NIL_ReplyCases.err_iff
#print axioms NIL_ReplyCases.err_iff
#check NIL_ReplyCases.fail_iff
#print axioms NIL_ReplyCases.fail_iff
#check NIL_ReplyCases.div_iff
#print axioms NIL_ReplyCases.div_iff
#check NIL_HistoryWindows.round0
#print axioms NIL_HistoryWindows.round0
#check NIL_HistoryWindows.round1_final
#print axioms NIL_HistoryWindows.round1_final
#check AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.RPx_Deployed.deployed
