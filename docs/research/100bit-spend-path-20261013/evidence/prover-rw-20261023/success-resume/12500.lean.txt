-- One focused audit of new declarations; no release or package replay.
import R1Z.ProverRwBodyCandidateData
import R1Z.ProverRwBodyCandidateStore
import R1Z.ProverRwBodyDataCriterion
import R1Z.ProverRwBodyReservationTransport
import R1Z.ProverRwBodyStore
import R1Z.ProverRwBodyStoreSource
import R1Z.ProverRwOrderedBounds
import R1Z.ProverRwOrderedMonad
import R1Z.ProverRwOrderedOracle
import R1Z.ProverRwOrderedPrefix
import R1Z.ProverRwOrderedPublication
import R1Z.ProverRwOrderedQueries
import R1Z.ProverRwOrderedQueryBounds
import R1Z.ProverRwOrderedQueryErase
import R1Z.ProverRwOrderedQuerySource
import R1Z.ProverRwSuccessArithmeticTotal
import R1Z.ProverRwSuccessArrayFromFn
import R1Z.ProverRwSuccessBodyInterpretation
import R1Z.ProverRwSuccessByteEquality
import R1Z.ProverRwSuccessCoefficientsSource
import R1Z.ProverRwSuccessComplexInverseExact
import R1Z.ProverRwSuccessComplexOperations
import R1Z.ProverRwSuccessEquality
import R1Z.ProverRwSuccessInverseInstall
import R1Z.ProverRwSuccessInverseTotal
import R1Z.ProverRwSuccessInverseZero
import R1Z.ProverRwSuccessPointsCaller
import R1Z.ProverRwSuccessPointsFinite
import R1Z.ProverRwSuccessPointsSource
import R1Z.ProverRwSuccessPointsTotal
import R1Z.ProverRwSuccessPowerExact
import R1Z.ProverRwSuccessPowerTotal
import R1Z.ProverRwSuccessQuarticInverseExact
import R1Z.ProverRwSuccessQuarticOperations
import R1Z.ProverRwSuccessQuarticTotal
import R1Z.ProverRwSuccessReverseRange
import R1Z.ProverRwSuccessScalarInverseExact
import R1Z.ProverRwSuccessVectors
import R1Z.ProverRwSuccessWideInverseAlgebra
import R1Z.ProverRwSuccessWideInverseExact
import R1Z.ProverRwSuccessWideInverseExecution
import R1Z.ProverRwSuccessWideNormalize
import R1Z.ProverRwSuccessWideSource
import R1Z.ProverRwSuccessWireInstall
import R1Z.ProverRwSuccessWireSource
import R1Z.ProverCommitDeployedFuel22

#print axioms R1Z.ProverRwBodyCandidateData.data_withState
#print axioms R1Z.ProverRwBodyCandidateData.keeps_withState
#print axioms R1Z.ProverRwBodyCandidateData.refinement_of_data
#print axioms R1Z.ProverRwBodyCandidateStore.points
#print axioms R1Z.ProverRwBodyCandidateStore.writeback
#print axioms R1Z.ProverRwBodyDataCriterion.eq_of_data
#print axioms R1Z.ProverRwBodyDataCriterion.continuation
#print axioms R1Z.ProverRwBodyReservationTransport.transfer
#print axioms R1Z.ProverRwBodyReservationTransport.callback_writeback
#print axioms R1Z.ProverRwBodyReservationTransport.body_writeback
#print axioms R1Z.ProverRwBodyStore.ok_keeps
#print axioms R1Z.ProverRwBodyStore.bind_keeps
#print axioms R1Z.ProverRwBodyStore.factor
#print axioms R1Z.ProverRwBodyStore.continuation
#print axioms R1Z.ProverRwOrderedBounds.bind_bound
#print axioms R1Z.ProverRwOrderedBounds.native_bound
#print axioms R1Z.ProverRwOrderedBounds.query_bound
#print axioms R1Z.ProverRwOrderedBounds.pure_bound
#print axioms R1Z.ProverRwOrderedMonad.result_bind
#print axioms R1Z.ProverRwOrderedMonad.history_bind
#print axioms R1Z.ProverRwOrderedOracle.result_bind
#print axioms R1Z.ProverRwOrderedOracle.result_native
#print axioms R1Z.ProverRwOrderedOracle.result_query
#print axioms R1Z.ProverRwOrderedOracle.result_pure
#print axioms R1Z.ProverRwOrderedOracle.failed_keeps_history
#print axioms R1Z.ProverRwOrderedOracle.diverged_keeps_history
#print axioms R1Z.ProverRwOrderedPrefix.erase
#print axioms R1Z.ProverRwOrderedPrefix.source
#print axioms R1Z.ProverRwOrderedPrefix.ordered
#print axioms R1Z.ProverRwOrderedPrefix.bound
#print axioms R1Z.ProverRwOrderedPublication.history
#print axioms R1Z.ProverRwOrderedQueries.source
#print axioms R1Z.ProverRwOrderedQueries.bound
#print axioms R1Z.ProverRwOrderedQueryBounds.absorb
#print axioms R1Z.ProverRwOrderedQueryBounds.materializeK
#print axioms R1Z.ProverRwOrderedQueryErase.absorb
#print axioms R1Z.ProverRwOrderedQueryErase.materializeK
#print axioms R1Z.ProverRwOrderedQueryErase.materialize
#print axioms R1Z.ProverRwSuccessArithmeticTotal.ok_total
#print axioms R1Z.ProverRwSuccessArithmeticTotal.bind_total
#print axioms R1Z.ProverRwSuccessArithmeticTotal.mapped_total
#print axioms R1Z.ProverRwSuccessArithmeticTotal.m_add
#print axioms R1Z.ProverRwSuccessArithmeticTotal.m_sub
#print axioms R1Z.ProverRwSuccessArithmeticTotal.m_mul
#print axioms R1Z.ProverRwSuccessArithmeticTotal.m_reduce
#print axioms R1Z.ProverRwSuccessArithmeticTotal.m_neg
#print axioms R1Z.ProverRwSuccessArithmeticTotal.c_mul
#print axioms R1Z.ProverRwSuccessArithmeticTotal.c_sub
#print axioms R1Z.ProverRwSuccessArithmeticTotal.c_neg
#print axioms R1Z.ProverRwSuccessArrayFromFn.run_pure
#print axioms R1Z.ProverRwSuccessArrayFromFn.fromFn_pure
#print axioms R1Z.ProverRwSuccessBodyInterpretation.points_source
#print axioms R1Z.ProverRwSuccessBodyInterpretation.coefficients_s2
#print axioms R1Z.ProverRwSuccessBodyInterpretation.coefficients_d
#print axioms R1Z.ProverRwSuccessByteEquality.list_compare
#print axioms R1Z.ProverRwSuccessByteEquality.array_eq
#print axioms R1Z.ProverRwSuccessComplexInverseExact.inverse
#print axioms R1Z.ProverRwSuccessComplexOperations.mul
#print axioms R1Z.ProverRwSuccessComplexOperations.sub
#print axioms R1Z.ProverRwSuccessComplexOperations.neg
#print axioms R1Z.ProverRwSuccessEquality.point_total
#print axioms R1Z.ProverRwSuccessEquality.context_total
#print axioms R1Z.ProverRwSuccessInverseInstall.m_source
#print axioms R1Z.ProverRwSuccessInverseInstall.q_source
#print axioms R1Z.ProverRwSuccessInverseInstall.neg_source
#print axioms R1Z.ProverRwSuccessInverseInstall.m_total
#print axioms R1Z.ProverRwSuccessInverseTotal.c_inv_total
#print axioms R1Z.ProverRwSuccessInverseTotal.c_mul_total
#print axioms R1Z.ProverRwSuccessInverseTotal.c_sub_total
#print axioms R1Z.ProverRwSuccessInverseTotal.c_neg_total
#print axioms R1Z.ProverRwSuccessInverseTotal.q_inv_total
#print axioms R1Z.ProverRwSuccessInverseTotal.q_neg_total
#print axioms R1Z.ProverRwSuccessInverseZero.m_zero
#print axioms R1Z.ProverRwSuccessInverseZero.c_zero
#print axioms R1Z.ProverRwSuccessPointsCaller.source_total
#print axioms R1Z.ProverRwSuccessPointsCaller.installed_total
#print axioms R1Z.ProverRwSuccessPointsFinite.source
#print axioms R1Z.ProverRwSuccessPointsTotal.update_total
#print axioms R1Z.ProverRwSuccessPointsTotal.finite_total
#print axioms R1Z.ProverRwSuccessPointsTotal.loop_total
#print axioms R1Z.ProverRwSuccessPowerExact.bit_val
#print axioms R1Z.ProverRwSuccessPowerExact.power_step
#print axioms R1Z.ProverRwSuccessPowerExact.exact_result
#print axioms R1Z.ProverRwSuccessPowerTotal.mul_total
#print axioms R1Z.ProverRwSuccessPowerTotal.shift
#print axioms R1Z.ProverRwSuccessPowerTotal.loop_bind
#print axioms R1Z.ProverRwSuccessPowerTotal.pow_unfold
#print axioms R1Z.ProverRwSuccessPowerTotal.pow_total
#print axioms R1Z.ProverRwSuccessQuarticInverseExact.r_canonical
#print axioms R1Z.ProverRwSuccessQuarticInverseExact.r_value
#print axioms R1Z.ProverRwSuccessQuarticInverseExact.inverse
#print axioms R1Z.ProverRwSuccessQuarticOperations.mul
#print axioms R1Z.ProverRwSuccessQuarticOperations.sub
#print axioms R1Z.ProverRwSuccessQuarticOperations.neg
#print axioms R1Z.ProverRwSuccessQuarticTotal.c_add
#print axioms R1Z.ProverRwSuccessQuarticTotal.m_double
#print axioms R1Z.ProverRwSuccessQuarticTotal.c_r
#print axioms R1Z.ProverRwSuccessQuarticTotal.q_add
#print axioms R1Z.ProverRwSuccessQuarticTotal.q_sub
#print axioms R1Z.ProverRwSuccessQuarticTotal.q_mul
#print axioms R1Z.ProverRwSuccessQuarticTotal.add
#print axioms R1Z.ProverRwSuccessQuarticTotal.sub
#print axioms R1Z.ProverRwSuccessQuarticTotal.mul
#print axioms R1Z.ProverRwSuccessReverseRange.pred_val
#print axioms R1Z.ProverRwSuccessReverseRange.next_zero
#print axioms R1Z.ProverRwSuccessReverseRange.next_pos
#print axioms R1Z.ProverRwSuccessScalarInverseExact.exponent_val
#print axioms R1Z.ProverRwSuccessScalarInverseExact.exact_result
#print axioms R1Z.ProverRwSuccessScalarInverseExact.canonical_injective
#print axioms R1Z.ProverRwSuccessScalarInverseExact.fixed_chain
#print axioms R1Z.ProverRwSuccessVectors.pop_payload
#print axioms R1Z.ProverRwSuccessVectors.empty_test
#print axioms R1Z.ProverRwSuccessVectors.empty_value
#print axioms R1Z.ProverRwSuccessVectors.array_accept
#print axioms R1Z.ProverRwSuccessVectors.array_reject
#print axioms R1Z.ProverRwSuccessWideInverseAlgebra.norm_value
#print axioms R1Z.ProverRwSuccessWideInverseAlgebra.inverse_coordinates
#print axioms R1Z.ProverRwSuccessWideInverseExact.u_canonical
#print axioms R1Z.ProverRwSuccessWideInverseExact.u_value
#print axioms R1Z.ProverRwSuccessWideInverseExact.norm_value
#print axioms R1Z.ProverRwSuccessWideInverseExact.inverse
#print axioms R1Z.ProverRwSuccessWideInverseExecution.execute
#print axioms R1Z.ProverRwSuccessWideNormalize.word_fixed
#print axioms R1Z.ProverRwSuccessWideNormalize.fixed
#print axioms R1Z.ProverRwSuccessWideNormalize.construct
#print axioms R1Z.ProverRwSuccessWideSource.neg_installed
#print axioms R1Z.ProverRwSuccessWideSource.inverse_installed
#print axioms R1Z.ProverRwSuccessWireInstall.domain_source
#print axioms R1Z.ProverRwSuccessWireInstall.domain_length

#print R1Z.ProverCommitDeployedFuel22.RustProverRefinement
