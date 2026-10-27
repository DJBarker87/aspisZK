import LPa_AddFormula
import LPa_AddInvariant
import LPa_ArithmeticInspect
import LPa_Boundary
import LPa_BoundaryPure
import LPa_BoundaryWitness
import LPa_ByteBound
import LPa_ByteLoop
import LPa_CanonicalAdd
import LPa_Check
import LPa_CheckLaws
import LPa_Circle
import LPa_Claims
import LPa_ClaimsFold
import LPa_Decode
import LPa_DecodeLaws
import LPa_Dot
import LPa_DotTotal
import LPa_Echeck
import LPa_EcheckLaws
import LPa_Expand
import LPa_ExpansionLaws
import LPa_FirstError
import LPa_Fold
import LPa_Map
import LPa_MonadicFold
import LPa_Nonvacuity
import LPa_PureFold
import LPa_ScanCongruence
import LPa_Slices
import LPa_StageLaws
import LPa_Validate
import LPa_ValidateLaws
import LPa_View
import LPa_ViewFrozen
import LPa_ViewRejected
import LPa_Word

#print axioms LPa.stages_fold
#print axioms LPa.stages_all
#print axioms LPa.stages_append
#print axioms LPa.build_map
#print axioms LPa.build_fold
#print axioms LPa.firstBad_find
#print axioms LPa.firstBad_fold
#print axioms LPa.stagesM_fold
#print axioms LPa.walkM_fold
#print axioms LPa.Check.loop_eq_model
#print axioms LPa.Check.shipped_leaf_model
#print axioms LPa.Check.loop_eq_fold
#print axioms LPa.Echeck.loop_eq_model
#print axioms LPa.Echeck.shipped_leaf_model
#print axioms LPa.Echeck.loop_eq_fold
#print axioms LPa.Validate.loop_eq_model
#print axioms LPa.Validate.loop_eq_fold
#print axioms LPa.Validate.shipped_leaf_model
#print axioms LPa.Expand.loop_eq_map
#print axioms LPa.Expand.loop_eq_fold
#print axioms LPa.Expand.shipped_leaf_model
#print axioms LPa.Decode.values_eq_map
#print axioms LPa.Decode.values_eq_fold
#print axioms LPa.Decode.shipped_leaf_model
#print axioms LPa.Boundary.loop_eq_model
#print axioms LPa.Boundary.loop_eq_fold
#print axioms LPa.Boundary.actual_bound
#print axioms LPa.Dot.loop_eq_map
#print axioms LPa.Dot.loop_eq_fold
#print axioms LPa.Dot.shipped_leaf_model
#print axioms LPa.Claims.loop_eq_fold
#print axioms LPa.Claims.leaf_call_order
#print axioms LPa.View.inactive_reject
#print axioms LPa.View.success
#print axioms LPa.Circle.leaf_eq_reference
#print axioms LPa.Circle.error_independent
#print axioms LPa.stages_congr
#print axioms LPa.firstBad_bound
#print axioms LPa.firstBad_none
#print axioms LPa.firstBad_is_bad
#print axioms LPa.build_length
#print axioms LPa.Check.accepts_iff
#print axioms LPa.Check.rejects_of_bad_stage
#print axioms LPa.Echeck.accepts_iff
#print axioms LPa.Echeck.rejects_of_bad_stage
#print axioms LPa.Validate.error_index_bound
#print axioms LPa.Validate.error_exact
#print axioms LPa.Validate.accepts_of_all_stages
#print axioms LPa.Expand.loop_length
#print axioms LPa.Expand.low_half
#print axioms LPa.Expand.high_half
#print axioms LPa.Expand.y1_loop_fold
#print axioms LPa.Decode.values_length
#print axioms LPa.Decode.first_error_bound
#print axioms LPa.Decode.accepted_values
#print axioms LPa.Nonvacuity.check_accepts
#print axioms LPa.Nonvacuity.echeck_accepts
#print axioms LPa.Nonvacuity.validate_accepts
#print axioms LPa.Nonvacuity.invalid_row_reached
#print axioms LPa.Bytes.decode_bound
#print axioms LPa.Bytes.le32_eq_decode
#print axioms LPa.Bytes.le32_bound
#print axioms LPa.Bytes.word_val
#print axioms LPa.Bytes.word_canonical_iff
#print axioms LPa.Bytes.little_fold
#print axioms LPa.Bytes.actual_word_loop
#print axioms LPa.Add.model_word
#print axioms LPa.Add.model_pair
#print axioms LPa.Add.model_field
#print axioms LPa.walkM_pure
#print axioms LPa.walkM_congr
#print axioms LPa.Boundary.loop_pure
#print axioms LPa.Claims.fromRecord_spec
#print axioms LPa.Claims.leaf_eq_loop
#print axioms LPa.Dot.loop_length
#print axioms LPa.Dot.model_total
#print axioms LPa.check_stage_congruence
#print axioms LPa.echeck_stage_congruence
#print axioms LPa.Slices.range_success
#print axioms LPa.Slices.segment_length
#print axioms LPa.View.frozen_success
#print axioms LPa.Add.word_val_canonical
#print axioms LPa.Add.word_canonical
#print axioms LPa.Add.field_canonical
#print axioms LPa.Add.fold_canonical
#print axioms LPa.Boundary.field_zero
#print axioms LPa.Boundary.fold_zero
#print axioms LPa.Boundary.zero_accepted
#print axioms LPa.View.frozen_reject
#print axioms compact.check_values
#print axioms verifier.echeck
#print axioms compact.expand_values
#print axioms verifier.candidate.wide_view
#print axioms r1_semantic.claims
#print axioms r1_wire.ValidatedRecord.decode_k
#print axioms r1_wire.validate_record_fields
#print axioms r1_semantic.semantic_boundary
#print axioms fast_pairing.canonical.Dot.push
#print axioms sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once
