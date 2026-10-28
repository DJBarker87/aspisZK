import NBG_Additive
import NBG_Atomic
import NBG_ByteAudit
import NBG_CheckedSub
import NBG_Constructors
import NBG_Embedding
import NBG_Error
import NBG_FieldDischarge
import NBG_FieldSquare
import NBG_GetterPorts
import NBG_Header
import NBG_InverseBridge
import NBG_PaymentChecks
import NBG_PaymentValidators
import NBG_Reducer
import NBG_Runtime
import NBG_SquareLoop
import NBG_SquareTrace
import NBG_Transport
import NBG_Utilities
import NBG_WideBytes
import NBG_WideCarriers
import NBG_WriterPorts
import NBC_Audit
set_option autoImplicit false
#print axioms NBG_Additive.m31_double
#print axioms NBG_Additive.cm31_double
#print axioms AspisR1.LPi_NatBase.add
#print axioms AspisR1.LPi_NatBase.sub
#print axioms AspisR1.LPi_FieldValues.cm_add
#print axioms AspisR1.LPi_FieldValues.cm_sub
#print axioms AspisR1.LPi_FieldValues.by_r
#print axioms AspisR1.LPi_TowerValues.qm_add
#print axioms AspisR1.LPi_TowerValues.qm_sub
#print axioms NBG_Atomic.unwrap_ok
#print axioms NBG_Atomic.unwrap_err
#print axioms NBG_Atomic.transfer_projection
#print axioms NBG_Atomic.withdrawal_projection
#print axioms NBG_Atomic.digest_canonical
#print axioms NBG_Atomic.m31_decode
#print axioms AspisR1.CandidateParserSupport.parser_refines_array
#print axioms AspisR1.CandidateCM31Parser.from_le_bytes_refines
#print axioms AspisR1.CandidateQM31Parser.from_le_bytes_refines
#print axioms AspisR1.LPi_ByteWord.source
#print axioms AspisR1.LPi_WriterValues.cm_writer
#print axioms AspisR1.LPi_WriterValues.qm_writer
#print axioms AspisR1.LPi_EWriter.source
#print axioms NBG_CheckedSub.m31
#print axioms NBG_CheckedSub.cm_result
#print axioms NBG_CheckedSub.qm_result
#print axioms NBG_CheckedSub.wide_result
#print axioms NBG_Constructors.cm31_new
#print axioms NBG_Constructors.qm31_from_cm31
#print axioms NBG_Embedding.from_m31_result
#print axioms NBG_Embedding.from_qm31_result
#print axioms AspisS1M31Embedding.Total.reduce_val
#print axioms NBG_Error.transition
#print axioms NBG_FieldDischarge.canonical_fio
#print axioms NBG_FieldDischarge.wide_scale
#print axioms NBG_FieldDischarge.wide_qm
#print axioms AspisR1.LPf_BaseMultiply.source
#print axioms AspisR1.LPi_FieldValues.cm_mul
#print axioms AspisR1.LPi_TowerValues.qm_mul
#print axioms AspisR1.LPi_TowerValues.wide_mul
#print axioms AspisR1.LPi_TowerValues.mul_u
#print axioms AspisR1.LPi_MixedValues.cm_m31
#print axioms AspisR1.LPi_MixedValues.qm_m31
#print axioms NBG_FieldSquare.sub_word
#print axioms NBG_FieldSquare.input_value
#print axioms NBG_FieldSquare.cm_square
#print axioms NBG_FieldSquare.qm_square
#print axioms NBG_GetterPorts.c0
#print axioms NBG_GetterPorts.c1
#print axioms NBG_Header.tag_result
#print axioms NBG_Header.slice_equal
#print axioms NBG_Header.header_result
#print axioms NBG_InverseBridge.mul_eq_probe
#print axioms NBG_InverseBridge.inverse_result
#print axioms NBG_PaymentChecks.canonical_result
#print axioms NBG_PaymentChecks.zero_result
#print axioms NBG_PaymentChecks.capacity_result
#print axioms NBG_PaymentChecks.common_result
#print axioms NBG_PaymentValidators.transfer_result
#print axioms NBG_PaymentValidators.value_limit
#print axioms NBG_PaymentValidators.withdrawal_result
#print axioms NBG_Reducer.m31_reduce
#print axioms AspisR1.LPf_CoreReduction.source
#print axioms NBG_Runtime.digest_transition
#print axioms NBG_SquareLoop.mul_total
#print axioms NBG_SquareLoop.mul_refines
#print axioms NBG_SquareLoop.square_n_result
#print axioms NBG_Transport.folds_result
#print axioms NBG_Transport.tag_result
#print axioms NBG_Transport.final_len_result
#print axioms NBG_Transport.checkpoint_size_result
#print axioms NBG_Utilities.shape
#print axioms NBG_Utilities.lists
#print axioms NBG_WideBytes.bytes_result
#print axioms NBG_WideCarriers.wide_add
#print axioms NBG_WideCarriers.limbs_result
#print axioms NBG_WideCarriers.to_limbs_result
#print axioms NBG_WideCarriers.wrong_byte_length
#print axioms NBG_WideCarriers.remainder
#print axioms NBG_WideCarriers.canonical_qm31
#print axioms NBG_WideCarriers.wide_new
#print axioms NBG_WriterPorts.writer_result
#print axioms NBG_WriterPorts.word_order

#print axioms NBG_SquareTrace.loop_result
#print axioms NBG_SquareTrace.native_result
