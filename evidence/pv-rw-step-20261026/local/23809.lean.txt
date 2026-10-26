import R1Z.PV_RW_Audit
import R1Z.PV_RW_CombinedBodyData
import R1Z.PV_RW_CombinedCompression
import R1Z.PV_RW_CompressBodyData
import R1Z.PV_RW_CompressBound
import R1Z.PV_RW_CompressClosed
import R1Z.PV_RW_CompressClosedBodyData
import R1Z.PV_RW_CompressClosedFold
import R1Z.PV_RW_CompressClosedTotal
import R1Z.PV_RW_CompressConcrete
import R1Z.PV_RW_CompressConcreteBinding
import R1Z.PV_RW_CompressDictionaries
import R1Z.PV_RW_CompressEmission
import R1Z.PV_RW_CompressIterator
import R1Z.PV_RW_CompressLiftSelectors
import R1Z.PV_RW_CompressNativeBodyData
import R1Z.PV_RW_CompressNativeControl
import R1Z.PV_RW_CompressNativePower
import R1Z.PV_RW_CompressNativeState
import R1Z.PV_RW_CompressNativeTotal
import R1Z.PV_RW_CompressPowerChunk
import R1Z.PV_RW_CompressPowerChunks16
import R1Z.PV_RW_CompressPowerFold
import R1Z.PV_RW_CompressPowerLength
import R1Z.PV_RW_CompressPowerStep
import R1Z.PV_RW_CompressPowerTotal
import R1Z.PV_RW_CompressReference
import R1Z.PV_RW_CompressSelectors
import R1Z.PV_RW_CompressStep
import R1Z.PV_RW_Cursor
import R1Z.PV_RW_CursorFuel
import R1Z.PV_RW_CursorLoop
import R1Z.PV_RW_CursorMap
import R1Z.PV_RW_CursorRefinement
import R1Z.PV_RW_CursorRefinementExact
import R1Z.PV_RW_CursorTrace
import R1Z.PV_RW_DataParts
import R1Z.PV_RW_DataPartsIff
import R1Z.PV_RW_DataProduct
import R1Z.PV_RW_IteratorMeasure
import R1Z.PV_RW_IteratorSource
import R1Z.PV_RW_IteratorStateBound
import R1Z.PV_RW_IteratorStateConcat
import R1Z.PV_RW_IteratorStateFacts
import R1Z.PV_RW_IteratorStateLoop
import R1Z.PV_RW_IteratorStateSource
import R1Z.PV_RW_NativeCursor
import R1Z.PV_RW_NativeForBound
import R1Z.PV_RW_NativeForConcat
import R1Z.PV_RW_NativeForList
import R1Z.PV_RW_NativeForModel
import R1Z.PV_RW_NativeForRefinement
import R1Z.PV_RW_NativeForSource
import R1Z.PV_RW_Outcome
import R1Z.PV_RW_OutcomeIso
import R1Z.PV_RW_OutcomeProduct
import R1Z.PV_RW_OutcomeSumProduct
import R1Z.PV_RW_ResultListRun
import R1Z.PV_RW_ResultListTotal
import R1Z.PV_RW_ResultOutcome
import R1Z.PV_RW_SamplerArrayBound
import R1Z.PV_RW_SamplerArrayLegacy
import R1Z.PV_RW_SamplerArraySource
import R1Z.PV_RW_SamplerLimbBounds
import R1Z.PV_RW_SamplerLimbSource
import R1Z.PV_RW_SamplerLimbTotal
import R1Z.PV_RW_SamplerPass
import R1Z.PV_RW_SliceIterator
import R1Z.PrivacyR1HeadlineDeployedReal
-- One final frozen focused manifest with complete axioms audit; no full release/source replay claim.
#print axioms R1Z.PV_RW_CombinedBodyData.dictionaries
#print axioms R1Z.PV_RW_CombinedBodyData.caller
#print axioms R1Z.PV_RW_CombinedBodyData.refinement_of_data
#print axioms R1Z.PV_RW_CombinedCompression.control
#print axioms R1Z.PV_RW_CombinedCompression.owned
#print axioms R1Z.PV_RW_CombinedCompression.arity16
#print axioms R1Z.PV_RW_CombinedCompression.total
#print axioms R1Z.PV_RW_CompressBodyData.caller
#print axioms R1Z.PV_RW_CompressBodyData.refinement_of_data
#print axioms R1Z.PV_RW_CompressBound.sufficient
#print axioms R1Z.PV_RW_CompressBound.arity16
#print axioms R1Z.PV_RW_CompressBound.prefix_steps
#print axioms R1Z.PV_RW_CompressBound.iterator_bound
#print axioms R1Z.PV_RW_CompressClosed.source
#print axioms R1Z.PV_RW_CompressClosed.reference
#print axioms R1Z.PV_RW_CompressClosed.owned_equal
#print axioms R1Z.PV_RW_CompressClosed.source_arity16
#print axioms R1Z.PV_RW_CompressClosedBodyData.dictionaries
#print axioms R1Z.PV_RW_CompressClosedBodyData.caller
#print axioms R1Z.PV_RW_CompressClosedBodyData.refinement_of_data
#print axioms R1Z.PV_RW_CompressClosedFold.emitted_closed
#print axioms R1Z.PV_RW_CompressClosedFold.reference
#print axioms R1Z.PV_RW_CompressClosedFold.owned_equal
#print axioms R1Z.PV_RW_CompressClosedFold.source_loop
#print axioms R1Z.PV_RW_CompressClosedTotal.fold
#print axioms R1Z.PV_RW_CompressClosedTotal.compress
#print axioms R1Z.PV_RW_CompressClosedTotal.owned_equal
#print axioms R1Z.PV_RW_CompressClosedTotal.owned
#print axioms R1Z.PV_RW_CompressConcrete.current_owned
#print axioms R1Z.PV_RW_CompressConcrete.total
#print axioms R1Z.PV_RW_CompressConcreteBinding.emitted_closed
#print axioms R1Z.PV_RW_CompressConcreteBinding.independent
#print axioms R1Z.PV_RW_CompressConcreteBinding.total
#print axioms R1Z.PV_RW_CompressDictionaries.equal
#print axioms R1Z.PV_RW_CompressEmission.emitted_step
#print axioms R1Z.PV_RW_CompressEmission.emitted_fold
#print axioms R1Z.PV_RW_CompressIterator.nil
#print axioms R1Z.PV_RW_CompressIterator.cons
#print axioms R1Z.PV_RW_CompressIterator.fold
#print axioms R1Z.PV_RW_CompressIterator.reference
#print axioms R1Z.PV_RW_CompressIterator.arity16
#print axioms R1Z.PV_RW_CompressLiftSelectors.complex
#print axioms R1Z.PV_RW_CompressLiftSelectors.quartic
#print axioms R1Z.PV_RW_CompressLiftSelectors.initial_state
#print axioms R1Z.PV_RW_CompressNativeBodyData.dictionaries
#print axioms R1Z.PV_RW_CompressNativeBodyData.caller
#print axioms R1Z.PV_RW_CompressNativeBodyData.refinement_of_data
#print axioms R1Z.PV_RW_CompressNativeControl.listRun
#print axioms R1Z.PV_RW_CompressNativeControl.closed
#print axioms R1Z.PV_RW_CompressNativeControl.owned
#print axioms R1Z.PV_RW_CompressNativeControl.arity16
#print axioms R1Z.PV_RW_CompressNativePower.final_power
#print axioms R1Z.PV_RW_CompressNativePower.arity16
#print axioms R1Z.PV_RW_CompressNativeState.whole_state
#print axioms R1Z.PV_RW_CompressNativeState.bounded_state
#print axioms R1Z.PV_RW_CompressNativeState.arity16
#print axioms R1Z.PV_RW_CompressNativeTotal.state
#print axioms R1Z.PV_RW_CompressNativeTotal.output
#print axioms R1Z.PV_RW_CompressNativeTotal.independent
#print axioms R1Z.PV_RW_CompressPowerChunk.append
#print axioms R1Z.PV_RW_CompressPowerChunks16.split
#print axioms R1Z.PV_RW_CompressPowerFold.projection
#print axioms R1Z.PV_RW_CompressPowerLength.equal_length
#print axioms R1Z.PV_RW_CompressPowerLength.arity16
#print axioms R1Z.PV_RW_CompressPowerStep.image
#print axioms R1Z.PV_RW_CompressPowerStep.projection
#print axioms R1Z.PV_RW_CompressPowerTotal.mul
#print axioms R1Z.PV_RW_CompressPowerTotal.run
#print axioms R1Z.PV_RW_CompressReference.reference
#print axioms R1Z.PV_RW_CompressReference.arity16
#print axioms R1Z.PV_RW_CompressSelectors.scale
#print axioms R1Z.PV_RW_CompressSelectors.add
#print axioms R1Z.PV_RW_CompressSelectors.mul
#print axioms R1Z.PV_RW_CompressStep.step_eq
#print axioms R1Z.PV_RW_CompressStep.run_congr
#print axioms R1Z.PV_RW_CompressStep.run_eq
#print axioms R1Z.PV_RW_CompressStep.owned_fold
#print axioms R1Z.PV_RW_CompressStep.shipped_fold
#print axioms R1Z.PV_RW_Cursor.initial
#print axioms R1Z.PV_RW_Cursor.some_step
#print axioms R1Z.PV_RW_Cursor.none_step
#print axioms R1Z.PV_RW_Cursor.backing
#print axioms R1Z.PV_RW_Cursor.contents_step
#print axioms R1Z.PV_RW_Cursor.remaining_length
#print axioms R1Z.PV_RW_Cursor.decreases
#print axioms R1Z.PV_RW_Cursor.exhausted
#print axioms R1Z.PV_RW_Cursor.bounded
#print axioms R1Z.PV_RW_CursorFuel.list_identity
#print axioms R1Z.PV_RW_CursorFuel.insufficient
#print axioms R1Z.PV_RW_CursorFuel.sufficient_iff
#print axioms R1Z.PV_RW_CursorFuel.sixteen_requires_seventeen
#print axioms R1Z.PV_RW_CursorLoop.complete
#print axioms R1Z.PV_RW_CursorLoop.exact_fuel
#print axioms R1Z.PV_RW_CursorLoop.arity16
#print axioms R1Z.PV_RW_CursorLoop.congr
#print axioms R1Z.PV_RW_CursorLoop.append
#print axioms R1Z.PV_RW_CursorLoop.fail_head
#print axioms R1Z.PV_RW_CursorLoop.div_head
#print axioms R1Z.PV_RW_CursorMap.index
#print axioms R1Z.PV_RW_CursorMap.length
#print axioms R1Z.PV_RW_CursorMap.remaining
#print axioms R1Z.PV_RW_CursorMap.remaining_length
#print axioms R1Z.PV_RW_CursorMap.next
#print axioms R1Z.PV_RW_CursorRefinement.bind_refines
#print axioms R1Z.PV_RW_CursorRefinement.list_refines
#print axioms R1Z.PV_RW_CursorRefinement.bounded_refines
#print axioms R1Z.PV_RW_CursorRefinementExact.bounded
#print axioms R1Z.PV_RW_CursorTrace.trace
#print axioms R1Z.PV_RW_CursorTrace.success_trace
#print axioms R1Z.PV_RW_CursorTrace.erase
#print axioms R1Z.PV_RW_DataParts.refinement_of_parts
#print axioms R1Z.PV_RW_DataPartsIff.exact_criterion
#print axioms R1Z.PV_RW_DataProduct.payload
#print axioms R1Z.PV_RW_DataProduct.joint
#print axioms R1Z.PV_RW_DataProduct.equal_iff
#print axioms R1Z.PV_RW_IteratorMeasure.positive
#print axioms R1Z.PV_RW_IteratorMeasure.successor
#print axioms R1Z.PV_RW_IteratorMeasure.exhausted
#print axioms R1Z.PV_RW_IteratorMeasure.suffix_length
#print axioms R1Z.PV_RW_IteratorMeasure.cursor_unique
#print axioms R1Z.PV_RW_IteratorMeasure.exact_fuel
#print axioms R1Z.PV_RW_IteratorSource.exact
#print axioms R1Z.PV_RW_IteratorSource.next_some
#print axioms R1Z.PV_RW_IteratorSource.next_none
#print axioms R1Z.PV_RW_IteratorSource.start
#print axioms R1Z.PV_RW_IteratorSource.full_poststate
#print axioms R1Z.PV_RW_IteratorStateBound.control
#print axioms R1Z.PV_RW_IteratorStateBound.sufficient
#print axioms R1Z.PV_RW_IteratorStateBound.arity16
#print axioms R1Z.PV_RW_IteratorStateConcat.split
#print axioms R1Z.PV_RW_IteratorStateFacts.stopped
#print axioms R1Z.PV_RW_IteratorStateFacts.active
#print axioms R1Z.PV_RW_IteratorStateFacts.total
#print axioms R1Z.PV_RW_IteratorStateLoop.control
#print axioms R1Z.PV_RW_IteratorStateLoop.owned
#print axioms R1Z.PV_RW_IteratorStateSource.control
#print axioms R1Z.PV_RW_NativeCursor.remaining
#print axioms R1Z.PV_RW_NativeCursor.next
#print axioms R1Z.PV_RW_NativeCursor.injective
#print axioms R1Z.PV_RW_NativeForBound.sufficient
#print axioms R1Z.PV_RW_NativeForBound.exact_fuel
#print axioms R1Z.PV_RW_NativeForBound.arity16
#print axioms R1Z.PV_RW_NativeForConcat.split
#print axioms R1Z.PV_RW_NativeForList.exact
#print axioms R1Z.PV_RW_NativeForList.initial
#print axioms R1Z.PV_RW_NativeForModel.bounded
#print axioms R1Z.PV_RW_NativeForModel.run
#print axioms R1Z.PV_RW_NativeForModel.congr
#print axioms R1Z.PV_RW_NativeForRefinement.bounded
#print axioms R1Z.PV_RW_NativeForRefinement.run
#print axioms R1Z.PV_RW_NativeForSource.body_some
#print axioms R1Z.PV_RW_NativeForSource.body_none
#print axioms R1Z.PV_RW_NativeForSource.run_unfold
#print axioms R1Z.PV_RW_NativeForSource.bounded_some
#print axioms R1Z.PV_RW_NativeForSource.bounded_none
#print axioms R1Z.PV_RW_NativeForSource.run_some
#print axioms R1Z.PV_RW_NativeForSource.run_none
#print axioms R1Z.PV_RW_Outcome.ok_bind
#print axioms R1Z.PV_RW_Outcome.fail_bind
#print axioms R1Z.PV_RW_Outcome.div_bind
#print axioms R1Z.PV_RW_Outcome.bind_ok
#print axioms R1Z.PV_RW_Outcome.assoc
#print axioms R1Z.PV_RW_Outcome.congr
#print axioms R1Z.PV_RW_Outcome.map_id
#print axioms R1Z.PV_RW_Outcome.map_comp
#print axioms R1Z.PV_RW_Outcome.map_bind
#print axioms R1Z.PV_RW_OutcomeIso.left_inverse
#print axioms R1Z.PV_RW_OutcomeIso.injective
#print axioms R1Z.PV_RW_OutcomeIso.equal_iff
#print axioms R1Z.PV_RW_OutcomeProduct.joint_injective
#print axioms R1Z.PV_RW_OutcomeProduct.equal_iff
#print axioms R1Z.PV_RW_OutcomeSumProduct.payload_injective
#print axioms R1Z.PV_RW_OutcomeSumProduct.joint_injective
#print axioms R1Z.PV_RW_OutcomeSumProduct.equal_iff
#print axioms R1Z.PV_RW_ResultListRun.model
#print axioms R1Z.PV_RW_ResultListRun.congr
#print axioms R1Z.PV_RW_ResultListTotal.total
#print axioms R1Z.PV_RW_ResultListTotal.append
#print axioms R1Z.PV_RW_ResultOutcome.roundtrip
#print axioms R1Z.PV_RW_ResultOutcome.outcome_roundtrip
#print axioms R1Z.PV_RW_ResultOutcome.bind
#print axioms R1Z.PV_RW_ResultOutcome.injective
#print axioms R1Z.PV_RW_ResultOutcome.equal_iff
#print axioms R1Z.PV_RW_SamplerArrayBound.unfold_loop
#print axioms R1Z.PV_RW_SamplerArrayBound.sufficient
#print axioms R1Z.PV_RW_SamplerArrayBound.arity8
#print axioms R1Z.PV_RW_SamplerArrayBound.harness_bound
#print axioms R1Z.PV_RW_SamplerArrayLegacy.body
#print axioms R1Z.PV_RW_SamplerArrayLegacy.loop
#print axioms R1Z.PV_RW_SamplerArrayLegacy.step_invariant
#print axioms R1Z.PV_RW_SamplerArrayLegacy.total
#print axioms R1Z.PV_RW_SamplerArraySource.body
#print axioms R1Z.PV_RW_SamplerArraySource.loop_reference
#print axioms R1Z.PV_RW_SamplerArraySource.pass_reference
#print axioms R1Z.PV_RW_SamplerLimbBounds.positive
#print axioms R1Z.PV_RW_SamplerLimbBounds.dividend_bound
#print axioms R1Z.PV_RW_SamplerLimbBounds.dividend_fits
#print axioms R1Z.PV_RW_SamplerLimbBounds.remainder_preserved
#print axioms R1Z.PV_RW_SamplerLimbBounds.prefix_bound
#print axioms R1Z.PV_RW_SamplerLimbSource.limb
#print axioms R1Z.PV_RW_SamplerLimbTotal.divisor_value
#print axioms R1Z.PV_RW_SamplerLimbTotal.owned_total
#print axioms R1Z.PV_RW_SamplerLimbTotal.source_total
#print axioms R1Z.PV_RW_SamplerPass.congr
#print axioms R1Z.PV_RW_SamplerPass.source_owned
#print axioms R1Z.PV_RW_SamplerPass.total
#print axioms R1Z.PV_RW_SamplerPass.pass_source_owned
#print axioms R1Z.PV_RW_SliceIterator.start
#print axioms R1Z.PV_RW_SliceIterator.next_some
#print axioms R1Z.PV_RW_SliceIterator.next_none
#print axioms R1Z.PV_RW_SliceIterator.tail
#print axioms R1Z.PV_RW_SliceIterator.exhausted
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
