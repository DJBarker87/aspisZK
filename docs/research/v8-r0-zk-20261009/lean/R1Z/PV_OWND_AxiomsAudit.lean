import R1Z.PV_OWND_ActualBytes
import R1Z.PV_OWND_ActualFields
import R1Z.PV_OWND_ActualHeader
import R1Z.PV_OWND_ActualInitialized
import R1Z.PV_OWND_ActualItems
import R1Z.PV_OWND_AllocationBuffer
import R1Z.PV_OWND_Append00
import R1Z.PV_OWND_Append01
import R1Z.PV_OWND_Append02
import R1Z.PV_OWND_Append03
import R1Z.PV_OWND_Append04
import R1Z.PV_OWND_Append05
import R1Z.PV_OWND_Append06
import R1Z.PV_OWND_Append07
import R1Z.PV_OWND_Append08
import R1Z.PV_OWND_Append09
import R1Z.PV_OWND_Append10
import R1Z.PV_OWND_Append11
import R1Z.PV_OWND_Append12
import R1Z.PV_OWND_Append13
import R1Z.PV_OWND_Append14
import R1Z.PV_OWND_Append15
import R1Z.PV_OWND_Append16
import R1Z.PV_OWND_Append17
import R1Z.PV_OWND_Append18
import R1Z.PV_OWND_Append19
import R1Z.PV_OWND_AppendPhase
import R1Z.PV_OWND_CheckResult
import R1Z.PV_OWND_CheckSource
import R1Z.PV_OWND_CounterBounds
import R1Z.PV_OWND_CounterBranch
import R1Z.PV_OWND_CounterFrame
import R1Z.PV_OWND_CounterLoop
import R1Z.PV_OWND_CounterOrder
import R1Z.PV_OWND_EndpointCounter
import R1Z.PV_OWND_FixedPhases
import R1Z.PV_OWND_InitialAbort
import R1Z.PV_OWND_InitialBytes
import R1Z.PV_OWND_InitialCheck
import R1Z.PV_OWND_InitialContext
import R1Z.PV_OWND_InitialDrop
import R1Z.PV_OWND_InitialFailure
import R1Z.PV_OWND_InitialIdentity
import R1Z.PV_OWND_InitialNormal
import R1Z.PV_OWND_InitialNull
import R1Z.PV_OWND_InitialProgram
import R1Z.PV_OWND_InitialRun
import R1Z.PV_OWND_InitialSuccess
import R1Z.PV_OWND_InitialWorldFrame
import R1Z.PV_OWND_LegacyCount
import R1Z.PV_OWND_LegacySource
import R1Z.PV_OWND_LoanFresh
import R1Z.PV_OWND_PaddedFold
import R1Z.PV_OWND_PaddedFrame
import R1Z.PV_OWND_PaddedHeader
import R1Z.PV_OWND_PaddedValid
import R1Z.PV_OWND_PaddedValues
import R1Z.PV_OWND_Private00
import R1Z.PV_OWND_Private01
import R1Z.PV_OWND_Private02
import R1Z.PV_OWND_Private03
import R1Z.PV_OWND_Private04
import R1Z.PV_OWND_Private05
import R1Z.PV_OWND_Private06
import R1Z.PV_OWND_Private07
import R1Z.PV_OWND_Private08
import R1Z.PV_OWND_Private09
import R1Z.PV_OWND_Private10
import R1Z.PV_OWND_Private11
import R1Z.PV_OWND_Private12
import R1Z.PV_OWND_Private13
import R1Z.PV_OWND_Private14
import R1Z.PV_OWND_Private15
import R1Z.PV_OWND_Private16
import R1Z.PV_OWND_Private17
import R1Z.PV_OWND_Private18
import R1Z.PV_OWND_Private19
import R1Z.PV_OWND_Private20
import R1Z.PV_OWND_PrivatePhase
import R1Z.PV_OWND_PushCompose
import R1Z.PV_OWND_PushPrefix
import R1Z.PV_OWND_PushSuffix
import R1Z.PV_OWND_SourceBounds
import R1Z.PV_OWND_SourceShape
set_option autoImplicit false
#print axioms R1Z.PV_OWND_ActualBytes.valid
#print axioms R1Z.PV_OWND_ActualFields.represented
#print axioms R1Z.PV_OWND_ActualHeader.length
#print axioms R1Z.PV_OWND_ActualHeader.identity
#print axioms R1Z.PV_OWND_ActualHeader.values
#print axioms R1Z.PV_OWND_ActualInitialized.constructed
#print axioms R1Z.PV_OWND_ActualItems.source
#print axioms R1Z.PV_OWND_AllocationBuffer.valid
#print axioms R1Z.PV_OWND_Append00.source
#print axioms R1Z.PV_OWND_Append00.count
#print axioms R1Z.PV_OWND_Append01.source
#print axioms R1Z.PV_OWND_Append01.count
#print axioms R1Z.PV_OWND_Append02.source
#print axioms R1Z.PV_OWND_Append02.count
#print axioms R1Z.PV_OWND_Append03.source
#print axioms R1Z.PV_OWND_Append03.count
#print axioms R1Z.PV_OWND_Append04.source
#print axioms R1Z.PV_OWND_Append04.count
#print axioms R1Z.PV_OWND_Append05.source
#print axioms R1Z.PV_OWND_Append05.count
#print axioms R1Z.PV_OWND_Append06.source
#print axioms R1Z.PV_OWND_Append06.count
#print axioms R1Z.PV_OWND_Append07.source
#print axioms R1Z.PV_OWND_Append07.count
#print axioms R1Z.PV_OWND_Append08.source
#print axioms R1Z.PV_OWND_Append08.count
#print axioms R1Z.PV_OWND_Append09.source
#print axioms R1Z.PV_OWND_Append09.count
#print axioms R1Z.PV_OWND_Append10.source
#print axioms R1Z.PV_OWND_Append10.count
#print axioms R1Z.PV_OWND_Append11.source
#print axioms R1Z.PV_OWND_Append11.count
#print axioms R1Z.PV_OWND_Append12.source
#print axioms R1Z.PV_OWND_Append12.count
#print axioms R1Z.PV_OWND_Append13.source
#print axioms R1Z.PV_OWND_Append13.count
#print axioms R1Z.PV_OWND_Append14.source
#print axioms R1Z.PV_OWND_Append14.count
#print axioms R1Z.PV_OWND_Append15.source
#print axioms R1Z.PV_OWND_Append15.count
#print axioms R1Z.PV_OWND_Append16.source
#print axioms R1Z.PV_OWND_Append16.count
#print axioms R1Z.PV_OWND_Append17.source
#print axioms R1Z.PV_OWND_Append17.count
#print axioms R1Z.PV_OWND_Append18.source
#print axioms R1Z.PV_OWND_Append18.count
#print axioms R1Z.PV_OWND_Append19.source
#print axioms R1Z.PV_OWND_Append19.count
#print axioms R1Z.PV_OWND_AppendPhase.source
#print axioms R1Z.PV_OWND_AppendPhase.count
#print axioms R1Z.PV_OWND_CheckResult.success
#print axioms R1Z.PV_OWND_CheckResult.error_cleanup
#print axioms R1Z.PV_OWND_CheckSource.scalar_input
#print axioms R1Z.PV_OWND_CounterBounds.post_bound
#print axioms R1Z.PV_OWND_CounterBounds.byte_room
#print axioms R1Z.PV_OWND_CounterBranch.range_error
#print axioms R1Z.PV_OWND_CounterBranch.capacity_error
#print axioms R1Z.PV_OWND_CounterBranch.success
#print axioms R1Z.PV_OWND_CounterFrame.other
#print axioms R1Z.PV_OWND_CounterFrame.changed
#print axioms R1Z.PV_OWND_CounterLoop.bounds
#print axioms R1Z.PV_OWND_CounterOrder.producer_error
#print axioms R1Z.PV_OWND_CounterOrder.consumer_error
#print axioms R1Z.PV_OWND_CounterOrder.success
#print axioms R1Z.PV_OWND_FixedPhases.sponge_source
#print axioms R1Z.PV_OWND_FixedPhases.sponge_count
#print axioms R1Z.PV_OWND_FixedPhases.head_count
#print axioms R1Z.PV_OWND_FixedPhases.value_source
#print axioms R1Z.PV_OWND_FixedPhases.value_count
#print axioms R1Z.PV_OWND_FixedPhases.conservation_count
#print axioms R1Z.PV_OWND_FixedPhases.occupancy_count
#print axioms R1Z.PV_OWND_InitialAbort.null_abort
#print axioms R1Z.PV_OWND_InitialBytes.valid
#print axioms R1Z.PV_OWND_InitialBytes.length
#print axioms R1Z.PV_OWND_InitialBytes.capacity
#print axioms R1Z.PV_OWND_InitialBytes.values
#print axioms R1Z.PV_OWND_InitialContext.fresh
#print axioms R1Z.PV_OWND_InitialContext.noLoans
#print axioms R1Z.PV_OWND_InitialDrop.complete
#print axioms R1Z.PV_OWND_InitialFailure.failed
#print axioms R1Z.PV_OWND_InitialFailure.diverged
#print axioms R1Z.PV_OWND_InitialIdentity.append_identity
#print axioms R1Z.PV_OWND_InitialIdentity.initial_identity
#print axioms R1Z.PV_OWND_InitialNormal.complete
#print axioms R1Z.PV_OWND_InitialNull.complete
#print axioms R1Z.PV_OWND_InitialSuccess.complete
#print axioms R1Z.PV_OWND_InitialWorldFrame.retained
#print axioms R1Z.PV_OWND_InitialWorldFrame.heap_frame
#print axioms R1Z.PV_OWND_LegacyCount.private_count
#print axioms R1Z.PV_OWND_LegacyCount.append_count
#print axioms R1Z.PV_OWND_LegacyCount.count
#print axioms R1Z.PV_OWND_LoanFresh.fresh_noLoans
#print axioms R1Z.PV_OWND_PaddedFrame.header
#print axioms R1Z.PV_OWND_PaddedFrame.other
#print axioms R1Z.PV_OWND_PaddedHeader.length
#print axioms R1Z.PV_OWND_PaddedHeader.identity
#print axioms R1Z.PV_OWND_PaddedValid.valid
#print axioms R1Z.PV_OWND_PaddedValues.retained
#print axioms R1Z.PV_OWND_PaddedValues.suffix
#print axioms R1Z.PV_OWND_Private00.source
#print axioms R1Z.PV_OWND_Private00.base
#print axioms R1Z.PV_OWND_Private00.count
#print axioms R1Z.PV_OWND_Private01.source
#print axioms R1Z.PV_OWND_Private01.base
#print axioms R1Z.PV_OWND_Private01.count
#print axioms R1Z.PV_OWND_Private02.source
#print axioms R1Z.PV_OWND_Private02.base
#print axioms R1Z.PV_OWND_Private02.count
#print axioms R1Z.PV_OWND_Private03.source
#print axioms R1Z.PV_OWND_Private03.base
#print axioms R1Z.PV_OWND_Private03.count
#print axioms R1Z.PV_OWND_Private04.source
#print axioms R1Z.PV_OWND_Private04.base
#print axioms R1Z.PV_OWND_Private04.count
#print axioms R1Z.PV_OWND_Private05.source
#print axioms R1Z.PV_OWND_Private05.base
#print axioms R1Z.PV_OWND_Private05.count
#print axioms R1Z.PV_OWND_Private06.source
#print axioms R1Z.PV_OWND_Private06.base
#print axioms R1Z.PV_OWND_Private06.count
#print axioms R1Z.PV_OWND_Private07.source
#print axioms R1Z.PV_OWND_Private07.base
#print axioms R1Z.PV_OWND_Private07.count
#print axioms R1Z.PV_OWND_Private08.source
#print axioms R1Z.PV_OWND_Private08.base
#print axioms R1Z.PV_OWND_Private08.count
#print axioms R1Z.PV_OWND_Private09.source
#print axioms R1Z.PV_OWND_Private09.base
#print axioms R1Z.PV_OWND_Private09.count
#print axioms R1Z.PV_OWND_Private10.source
#print axioms R1Z.PV_OWND_Private10.base
#print axioms R1Z.PV_OWND_Private10.count
#print axioms R1Z.PV_OWND_Private11.source
#print axioms R1Z.PV_OWND_Private11.base
#print axioms R1Z.PV_OWND_Private11.count
#print axioms R1Z.PV_OWND_Private12.source
#print axioms R1Z.PV_OWND_Private12.base
#print axioms R1Z.PV_OWND_Private12.count
#print axioms R1Z.PV_OWND_Private13.source
#print axioms R1Z.PV_OWND_Private13.base
#print axioms R1Z.PV_OWND_Private13.count
#print axioms R1Z.PV_OWND_Private14.source
#print axioms R1Z.PV_OWND_Private14.base
#print axioms R1Z.PV_OWND_Private14.count
#print axioms R1Z.PV_OWND_Private15.source
#print axioms R1Z.PV_OWND_Private15.base
#print axioms R1Z.PV_OWND_Private15.count
#print axioms R1Z.PV_OWND_Private16.source
#print axioms R1Z.PV_OWND_Private16.base
#print axioms R1Z.PV_OWND_Private16.count
#print axioms R1Z.PV_OWND_Private17.source
#print axioms R1Z.PV_OWND_Private17.base
#print axioms R1Z.PV_OWND_Private17.count
#print axioms R1Z.PV_OWND_Private18.source
#print axioms R1Z.PV_OWND_Private18.base
#print axioms R1Z.PV_OWND_Private18.count
#print axioms R1Z.PV_OWND_Private19.source
#print axioms R1Z.PV_OWND_Private19.base
#print axioms R1Z.PV_OWND_Private19.count
#print axioms R1Z.PV_OWND_Private20.source
#print axioms R1Z.PV_OWND_Private20.base
#print axioms R1Z.PV_OWND_Private20.count
#print axioms R1Z.PV_OWND_PrivatePhase.source
#print axioms R1Z.PV_OWND_PrivatePhase.count
#print axioms R1Z.PV_OWND_PushCompose.append_eq
#print axioms R1Z.PV_OWND_PushPrefix.retained
#print axioms R1Z.PV_OWND_PushSuffix.suffix
#print axioms R1Z.PV_OWND_SourceBounds.private_aux
#print axioms R1Z.PV_OWND_SourceBounds.private_rows
#print axioms R1Z.PV_OWND_SourceBounds.append_rows
#print axioms R1Z.PV_OWND_SourceBounds.helper_success
#print axioms R1Z.PV_OWND_SourceBounds.helper_failure
#print axioms R1Z.PV_OWND_SourceBounds.word_room
#print axioms R1Z.PV_OWND_SourceShape.no_shape_error
#print axioms R1Z.PV_OWND_SourceShape.layout
