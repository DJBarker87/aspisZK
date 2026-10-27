import XRl_Adapter
import XRl_AdapterCounterexample
import XRl_AdapterErasure
import XRl_CanonicalConstructors
import XRl_CheckpointBytes
import XRl_CheckpointFinalizer
import XRl_ClosureAdapter
import XRl_ClosureCapture
import XRl_Collector
import XRl_DotAssociation
import XRl_DotHistory
import XRl_DotSums
import XRl_GeometryCollect
import XRl_GeometryInput
import XRl_GeometryLengths
import XRl_GeometryStep
import XRl_GeometryVectors
import XRl_InversionBoundary
import XRl_LineValues
import XRl_LoopInvariant
import XRl_MapCollector
import XRl_Nonvacuity
import XRl_QueryGeometry
import XRl_RangeMeasure
import XRl_ReverseCursor
import XRl_ReverseDomain
import XRl_SliceRemaining
import XRl_WideBoundary
import XRl_WideCanonical

#print axioms XRl_Adapter.closure_1_FnMut
#print axioms XRl_Adapter.closure_1_FnOnce_projection
#print axioms XRl_Adapter.closure_1_mut_once
#print axioms XRl_Adapter.closure_1_restoration
#print axioms XRl_Adapter.enumerateNext
#print axioms XRl_Adapter.enumerateRestored
#print axioms XRl_Adapter.exhausted_adapted
#print axioms XRl_Adapter.exhausted_original
#print axioms XRl_Adapter.exhausted_reachable
#print axioms XRl_Adapter.fresh_cursor
#print axioms XRl_Adapter.fromFnState
#print axioms XRl_Adapter.intoIter
#print axioms XRl_Adapter.next_back_cursor
#print axioms XRl_Adapter.next_back_not_equivalent
#print axioms XRl_Adapter.next_back_projection
#print axioms XRl_Adapter.next_back_restoration_cursor
#print axioms XRl_Adapter.next_projection
#print axioms XRl_Adapter.restoration_not_erasable
#print axioms XRl_Adapter.revRestored
#print axioms XRl_Adapter.reverseNext_at_zero
#print axioms XRl_Adapter.reverseNext_not_equivalent
#print axioms XRl_CanonicalConstructors.canon
#print axioms XRl_CanonicalConstructors.from_qm31
#print axioms XRl_CanonicalConstructors.new
#print axioms XRl_CanonicalConstructors.remainder
#print axioms XRl_CheckpointBytes.q_length
#print axioms XRl_CheckpointBytes.wide_total
#print axioms XRl_CheckpointBytes.word_length
#print axioms XRl_CheckpointFinalizer.size
#print axioms XRl_Collector.length
#print axioms XRl_DotAssociation.reached
#print axioms XRl_DotHistory.canonical_scalars
#print axioms XRl_DotHistory.count
#print axioms XRl_DotHistory.initial_count
#print axioms XRl_DotSums.cells
#print axioms XRl_DotSums.factor
#print axioms XRl_GeometryCollect.length
#print axioms XRl_GeometryCollect.list_length
#print axioms XRl_GeometryInput.range
#print axioms XRl_GeometryLengths.loop
#print axioms XRl_GeometryStep.step
#print axioms XRl_GeometryVectors.clone
#print axioms XRl_GeometryVectors.extend
#print axioms XRl_InversionBoundary.success
#print axioms XRl_InversionBoundary.zero_rejected
#print axioms XRl_LineValues.continuation
#print axioms XRl_LoopInvariant.preserve
#print axioms XRl_MapCollector.advance
#print axioms XRl_MapCollector.length
#print axioms XRl_MapCollector.terminal
#print axioms XRl_Nonvacuity.bad_wide_history
#print axioms XRl_Nonvacuity.empty_history
#print axioms XRl_Nonvacuity.validated_wide_domain
#print axioms XRl_QueryGeometry.lengths
#print axioms XRl_QueryGeometry.queryGeometryLineInvariant
#print axioms XRl_RangeMeasure.advance
#print axioms XRl_RangeMeasure.terminal
#print axioms XRl_SliceRemaining.advance
#print axioms XRl_SliceRemaining.terminal
#print axioms XRl_WideBoundary.invalid_coordinate
#print axioms XRl_WideBoundary.invalid_wide_accepted
#print axioms XRl_WideBoundary.unchecked_wide_projection
#print axioms XRl_WideCanonical.from_limbs
#print axioms XRl_WideCanonical.q
#print axioms XRl_WideCanonical.word
