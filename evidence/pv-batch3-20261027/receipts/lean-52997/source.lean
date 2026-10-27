import PV_B3_BoundedLoop
import PV_B3_BoundedPacket
import PV_B3_Copy_117_Funs
import PV_B3_Copy_117_Types
import PV_B3_FieldBind
import PV_B3_FieldCAdd
import PV_B3_FieldCDouble
import PV_B3_FieldCMul
import PV_B3_FieldCMulR
import PV_B3_FieldCScale
import PV_B3_FieldCSquare
import PV_B3_FieldCSub
import PV_B3_FieldQAdd
import PV_B3_FieldQMul
import PV_B3_FieldQScale
import PV_B3_FieldQSquare
import PV_B3_FieldReduce
import PV_B3_FieldScalar
import PV_B3_FieldTransport
import PV_B3_Forest_134_Funs
import PV_B3_Forest_134_Types
import PV_B3_HostMulR
import PV_B3_LinearsCounter
import PV_B3_LinearsFinite
import PV_B3_LinearsGuard
import PV_B3_LinearsRank
import PV_B3_Mask117Fidelity
import PV_B3_Mask117Finite
import PV_B3_MaskArray
import PV_B3_MaskBump
import PV_B3_MaskCounter
import PV_B3_MaskFidelity
import PV_B3_MaskFinite
import PV_B3_MaskGuard
import PV_B3_MaskLoopDone
import PV_B3_MaskLoopStop
import PV_B3_MaskRank
import PV_B3_PolynomialCounter
import PV_B3_PolynomialEmission
import PV_B3_PolynomialFidelity
import PV_B3_PolynomialFinite
import PV_B3_PolynomialRank
import PV_B3_PolynomialStop
import PV_B3_PowerTransport
import PV_B3_PrepareComponent
import PV_B3_PreparedCarrier
import PV_B3_PreparedComponent
import PV_B3_PreparedMul
import PV_B3_PreparedNew
import PV_B3_Result
-- One axioms audit over the exact private closure; no target theorem is assumed.
#print axioms PV_B3_BoundedLoop.bounded
#print axioms PV_B3_BoundedLoop.source_eq_bounded
#print axioms PV_B3_BoundedPacket.forest134
#print axioms PV_B3_BoundedPacket.mask117
#print axioms PV_B3_BoundedPacket.polynomial121
#print axioms PV_B3_Copy_117.aspis_core.field.CM31
#print axioms PV_B3_Copy_117.aspis_core.field.CM31.add
#print axioms PV_B3_Copy_117.aspis_core.field.CM31.double
#print axioms PV_B3_Copy_117.aspis_core.field.CM31.mul
#print axioms PV_B3_Copy_117.aspis_core.field.CM31.mul_m31
#print axioms PV_B3_Copy_117.aspis_core.field.CM31.new
#print axioms PV_B3_Copy_117.aspis_core.field.CM31.square
#print axioms PV_B3_Copy_117.aspis_core.field.CM31.sub
#print axioms PV_B3_Copy_117.aspis_core.field.M31
#print axioms PV_B3_Copy_117.aspis_core.field.M31.add
#print axioms PV_B3_Copy_117.aspis_core.field.M31.double
#print axioms PV_B3_Copy_117.aspis_core.field.M31.mul
#print axioms PV_B3_Copy_117.aspis_core.field.M31.neg
#print axioms PV_B3_Copy_117.aspis_core.field.M31.reduce_u64
#print axioms PV_B3_Copy_117.aspis_core.field.M31.sub
#print axioms PV_B3_Copy_117.aspis_core.field.P
#print axioms PV_B3_Copy_117.aspis_core.field.QM31
#print axioms PV_B3_Copy_117.aspis_core.field.QM31.ONE
#print axioms PV_B3_Copy_117.aspis_core.field.QM31.ZERO
#print axioms PV_B3_Copy_117.aspis_core.field.QM31.add
#print axioms PV_B3_Copy_117.aspis_core.field.QM31.mul
#print axioms PV_B3_Copy_117.aspis_core.field.QM31.mul_m31
#print axioms PV_B3_Copy_117.aspis_core.field.QM31.square
#print axioms PV_B3_Copy_117.aspis_core.field.ct.add
#print axioms PV_B3_Copy_117.aspis_core.field.ct.neg
#print axioms PV_B3_Copy_117.aspis_core.field.ct.reduce64
#print axioms PV_B3_Copy_117.aspis_core.field.ct.sub
#print axioms PV_B3_Copy_117.aspis_core.field.ct.subtract_p
#print axioms PV_B3_Copy_117.aspis_core.field.mul_by_r
#print axioms PV_B3_Copy_117.aspis_core.field.reduce_u64
#print axioms PV_B3_Copy_117.aspis_core.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE
#print axioms PV_B3_Copy_117.aspis_core.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS
#print axioms PV_B3_Copy_117.host_arithmetic.FACTOR_EXPONENTS
#print axioms PV_B3_Copy_117.host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
#print axioms PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier
#print axioms PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.mul
#print axioms PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.new
#print axioms PV_B3_Copy_117.host_arithmetic.accumulate_channels
#print axioms PV_B3_Copy_117.host_arithmetic.cm31_mul_i
#print axioms PV_B3_Copy_117.host_arithmetic.cm31_mul_r
#print axioms PV_B3_Copy_117.host_arithmetic.evaluate_state_only_polynomial
#print axioms PV_B3_Copy_117.host_arithmetic.evaluate_state_only_polynomial.block_value
#print axioms PV_B3_Copy_117.host_arithmetic.evaluate_state_only_polynomial_loop
#print axioms PV_B3_Copy_117.host_arithmetic.evaluate_state_only_polynomial_loop.body
#print axioms PV_B3_Copy_117.host_arithmetic.mask_only_coefficients
#print axioms PV_B3_Copy_117.host_arithmetic.mask_power_26
#print axioms PV_B3_Copy_117.host_arithmetic.mul_tower_basis
#print axioms PV_B3_Copy_117.host_arithmetic.prepare_component
#print axioms PV_B3_Copy_117.host_arithmetic.prepared_component_mul
#print axioms PV_B3_Copy_117.host_arithmetic.qm31_sum_products3
#print axioms PV_B3_Copy_117.host_arithmetic.reconstruct_channels
#print axioms PV_B3_Copy_117.host_arithmetic.reconstruct_component
#print axioms PV_B3_Copy_117.host_arithmetic.selected_coefficients
#print axioms PV_B3_Copy_117.host_arithmetic.selected_horner
#print axioms PV_B3_Copy_117.host_arithmetic.selected_mask_linears
#print axioms PV_B3_Copy_117.host_arithmetic.selected_mask_linears_loop
#print axioms PV_B3_Copy_117.host_arithmetic.selected_mask_linears_loop.body
#print axioms PV_B3_Copy_117.host_arithmetic.state_only_selected_mask_value
#print axioms PV_B3_FieldBind.bind_map
#print axioms PV_B3_FieldBind.transport
#print axioms PV_B3_FieldCAdd.source
#print axioms PV_B3_FieldCDouble.source
#print axioms PV_B3_FieldCMul.source
#print axioms PV_B3_FieldCMulR.source
#print axioms PV_B3_FieldCScale.source
#print axioms PV_B3_FieldCSquare.source
#print axioms PV_B3_FieldCSub.source
#print axioms PV_B3_FieldQAdd.source
#print axioms PV_B3_FieldQMul.source
#print axioms PV_B3_FieldQScale.source
#print axioms PV_B3_FieldQSquare.source
#print axioms PV_B3_FieldReduce.source
#print axioms PV_B3_FieldScalar.N.P
#print axioms PV_B3_FieldScalar.N.add
#print axioms PV_B3_FieldScalar.N.double
#print axioms PV_B3_FieldScalar.N.mul
#print axioms PV_B3_FieldScalar.N.neg
#print axioms PV_B3_FieldScalar.N.red
#print axioms PV_B3_FieldScalar.N.sub
#print axioms PV_B3_FieldScalar.N.subP
#print axioms PV_B3_FieldScalar.O.P
#print axioms PV_B3_FieldScalar.O.add
#print axioms PV_B3_FieldScalar.O.double
#print axioms PV_B3_FieldScalar.O.mul
#print axioms PV_B3_FieldScalar.O.neg
#print axioms PV_B3_FieldScalar.O.red
#print axioms PV_B3_FieldScalar.O.sub
#print axioms PV_B3_FieldScalar.O.subP
#print axioms PV_B3_FieldScalar.add
#print axioms PV_B3_FieldScalar.double
#print axioms PV_B3_FieldScalar.mul
#print axioms PV_B3_FieldScalar.neg
#print axioms PV_B3_FieldScalar.p
#print axioms PV_B3_FieldScalar.reduce
#print axioms PV_B3_FieldScalar.sub
#print axioms PV_B3_FieldScalar.subtract
#print axioms PV_B3_FieldTransport.New.C
#print axioms PV_B3_FieldTransport.New.Q
#print axioms PV_B3_FieldTransport.Old.C
#print axioms PV_B3_FieldTransport.Old.Q
#print axioms PV_B3_FieldTransport.c_left
#print axioms PV_B3_FieldTransport.c_right
#print axioms PV_B3_FieldTransport.fromC
#print axioms PV_B3_FieldTransport.fromQ
#print axioms PV_B3_FieldTransport.map
#print axioms PV_B3_FieldTransport.map_bind
#print axioms PV_B3_FieldTransport.map_comp
#print axioms PV_B3_FieldTransport.map_ok
#print axioms PV_B3_FieldTransport.q_left
#print axioms PV_B3_FieldTransport.q_right
#print axioms PV_B3_FieldTransport.toC
#print axioms PV_B3_FieldTransport.toQ
#print axioms PV_B3_Forest_134.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
#print axioms PV_B3_Forest_134.host_forest.MASK_LINKS
#print axioms PV_B3_Forest_134.host_forest.mask_endpoint_bump
#print axioms PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1
#print axioms PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop
#print axioms PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
#print axioms PV_B3_HostMulR.source
#print axioms PV_B3_LinearsCounter.Progress
#print axioms PV_B3_LinearsCounter.Q
#print axioms PV_B3_LinearsCounter.State
#print axioms PV_B3_LinearsCounter.body_counter
#print axioms PV_B3_LinearsFinite.body
#print axioms PV_B3_LinearsFinite.decreases
#print axioms PV_B3_LinearsFinite.source
#print axioms PV_B3_LinearsGuard.continued
#print axioms PV_B3_LinearsRank.decreases
#print axioms PV_B3_LinearsRank.decrement
#print axioms PV_B3_LinearsRank.rank
#print axioms PV_B3_Mask117Fidelity.Q
#print axioms PV_B3_Mask117Fidelity.result
#print axioms PV_B3_Mask117Fidelity.values
#print axioms PV_B3_Mask117Finite.Q
#print axioms PV_B3_Mask117Finite.linears
#print axioms PV_B3_Mask117Finite.linears_source
#print axioms PV_B3_Mask117Finite.reference
#print axioms PV_B3_Mask117Finite.source_complete
#print axioms PV_B3_MaskArray.mask_zero
#print axioms PV_B3_MaskArray.producer_zero
#print axioms PV_B3_MaskArray.repeat_read
#print axioms PV_B3_MaskBump.accept
#print axioms PV_B3_MaskBump.one
#print axioms PV_B3_MaskBump.reject
#print axioms PV_B3_MaskBump.small_cases
#print axioms PV_B3_MaskBump.zero
#print axioms PV_B3_MaskCounter.Final
#print axioms PV_B3_MaskCounter.Progress
#print axioms PV_B3_MaskCounter.State
#print axioms PV_B3_MaskCounter.body_counter
#print axioms PV_B3_MaskCounter.done_safe
#print axioms PV_B3_MaskFidelity.mask_values
#print axioms PV_B3_MaskFinite.body
#print axioms PV_B3_MaskFinite.decreases
#print axioms PV_B3_MaskFinite.loop_source
#print axioms PV_B3_MaskFinite.op134_bounded
#print axioms PV_B3_MaskFinite.reference
#print axioms PV_B3_MaskGuard.Guard
#print axioms PV_B3_MaskGuard.body_guard
#print axioms PV_B3_MaskGuard.continued_counter
#print axioms PV_B3_MaskLoopDone.source_done
#print axioms PV_B3_MaskLoopStop.body_done
#print axioms PV_B3_MaskRank.increment_value
#print axioms PV_B3_MaskRank.rank
#print axioms PV_B3_MaskRank.rank_decreases
#print axioms PV_B3_MaskRank.size_above_limit
#print axioms PV_B3_MaskRank.size_positive
#print axioms PV_B3_PolynomialCounter.Progress
#print axioms PV_B3_PolynomialCounter.Q
#print axioms PV_B3_PolynomialCounter.State
#print axioms PV_B3_PolynomialCounter.body_counter
#print axioms PV_B3_PolynomialFidelity.Q
#print axioms PV_B3_PolynomialFidelity.canonical_case
#print axioms PV_B3_PolynomialFidelity.raw_case
#print axioms PV_B3_PolynomialFidelity.values
#print axioms PV_B3_PolynomialFinite.body
#print axioms PV_B3_PolynomialFinite.decreases
#print axioms PV_B3_PolynomialFinite.loop_source
#print axioms PV_B3_PolynomialFinite.reference
#print axioms PV_B3_PolynomialFinite.source_complete
#print axioms PV_B3_PolynomialRank.decreases
#print axioms PV_B3_PolynomialRank.rank
#print axioms PV_B3_PolynomialStop.body_done
#print axioms PV_B3_PolynomialStop.loop_done
#print axioms PV_B3_PowerTransport.reference
#print axioms PV_B3_PowerTransport.source
#print axioms PV_B3_PrepareComponent.source
#print axioms PV_B3_PreparedCarrier.NewP
#print axioms PV_B3_PreparedCarrier.OldP
#print axioms PV_B3_PreparedCarrier.fromP
#print axioms PV_B3_PreparedCarrier.left
#print axioms PV_B3_PreparedCarrier.right
#print axioms PV_B3_PreparedCarrier.toP
#print axioms PV_B3_PreparedComponent.source
#print axioms PV_B3_PreparedMul.source
#print axioms PV_B3_PreparedNew.source
#print axioms PV_B3_Result.Safe
#print axioms PV_B3_Result.bind_any
#print axioms PV_B3_Result.bind_assoc
#print axioms PV_B3_Result.bind_success
