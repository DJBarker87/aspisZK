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
import R1Z.PV_RW_CompressReference
import R1Z.PV_RW_CompressSelectors
import R1Z.PV_RW_CompressStep
import R1Z.PV_RW_SamplerArrayBound
import R1Z.PV_RW_SamplerArrayLegacy
import R1Z.PV_RW_SamplerArraySource
import R1Z.PV_RW_SamplerLimbBounds
import R1Z.PV_RW_SamplerLimbSource
import R1Z.PV_RW_SamplerLimbTotal
import R1Z.PV_RW_SamplerPass
import R1Z.PrivacyR1HeadlineDeployedReal
-- Focused cached closure audit, not a coherent frozen release replay.
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
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
