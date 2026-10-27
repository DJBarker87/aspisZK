import R1Z.PV_Inv_BadContainment
import R1Z.PV_Inv_Circle
import R1Z.PV_Inv_CircleRecovery
import R1Z.PV_Inv_CompressTuple
import R1Z.PV_Inv_CompressionFinite
import R1Z.PV_Inv_EmbedTag
import R1Z.PV_Inv_GlobalOrigin
import R1Z.PV_Inv_GlobalProjection
import R1Z.PV_Inv_GlobalScan
import R1Z.PV_Inv_Guard
import R1Z.PV_Inv_IInterpolationBasis
import R1Z.PV_Inv_IInterpolationIndices
import R1Z.PV_Inv_IInterpolationPoly
import R1Z.PV_Inv_IM31Array
import R1Z.PV_Inv_InterpolationLoop
import R1Z.PV_Inv_ModelPack
import R1Z.PV_Inv_NativeCompress
import R1Z.PV_Inv_NativeInverseM
import R1Z.PV_Inv_NativeNormQ
import R1Z.PV_Inv_NativePackedTests
import R1Z.PV_Inv_NativeRegistry
import R1Z.PV_Inv_Norm
import R1Z.PV_Inv_Pack
import R1Z.PV_Inv_PackOperands
import R1Z.PV_Inv_PoleMass
import R1Z.PV_Inv_RawCanonical
import R1Z.PV_Inv_RawInvoke
import R1Z.PV_Inv_RawMapRun
import R1Z.PV_Inv_RawNative
import R1Z.PV_Inv_RawSchedule
import R1Z.PV_Inv_RawU32
import R1Z.PV_Inv_RegistrySlot
import R1Z.PV_Inv_ScanAppend
import R1Z.PV_Inv_ScanMask
import R1Z.PV_Inv_Sentinel
import R1Z.PV_Inv_SourceInverseTrace
import R1Z.PV_Inv_TupleModel
import R1Z.PV_Inv_WordTuple

/-! Focused final dependency/import and accepted-axioms audit. Not a frozen release replay. -/
#print axioms R1Z.PV_Inv_BadContainment.producer_zero_is_pole
#print axioms R1Z.PV_Inv_BadContainment.consumer_zero_is_pole
#print axioms R1Z.PV_Inv_Circle.denominator_factor
#print axioms R1Z.PV_Inv_Circle.singular_iff
#print axioms R1Z.PV_Inv_Circle.denominator_nonzero
#print axioms R1Z.PV_Inv_CircleRecovery.one_add_x
#print axioms R1Z.PV_Inv_CircleRecovery.inverse_parameter
#print axioms R1Z.PV_Inv_CircleRecovery.rational_injective
#print axioms R1Z.PV_Inv_CompressTuple.compress_exact
#print axioms R1Z.PV_Inv_CompressionFinite.weighted_ofFn
#print axioms R1Z.PV_Inv_CompressionFinite.tagged_sixteen
#print axioms R1Z.PV_Inv_EmbedTag.canonical
#print axioms R1Z.PV_Inv_EmbedTag.value
#print axioms R1Z.PV_Inv_GlobalOrigin.origin
#print axioms R1Z.PV_Inv_GlobalProjection.target
#print axioms R1Z.PV_Inv_GlobalProjection.other
#print axioms R1Z.PV_Inv_GlobalScan.native_guarded
#print axioms R1Z.PV_Inv_Guard.none_iff
#print axioms R1Z.PV_Inv_Guard.nonzero_branch
#print axioms R1Z.PV_Inv_Guard.difference
#print axioms R1Z.PV_Inv_Guard.guarded
#print axioms R1Z.PV_Inv_IInterpolationBasis.basis_value
#print axioms R1Z.PV_Inv_IInterpolationIndices.size_u8
#print axioms R1Z.PV_Inv_IInterpolationIndices.cast32_val
#print axioms R1Z.PV_Inv_IInterpolationIndices.cast32_canonical
#print axioms R1Z.PV_Inv_IInterpolationIndices.cast32_decode
#print axioms R1Z.PV_Inv_IInterpolationIndices.add_val
#print axioms R1Z.PV_Inv_IInterpolationIndices.next_val
#print axioms R1Z.PV_Inv_IInterpolationPoly.coeff
#print axioms R1Z.PV_Inv_IInterpolationPoly.mul_coeff
#print axioms R1Z.PV_Inv_IInterpolationPoly.mul_shape
#print axioms R1Z.PV_Inv_IM31Array.index
#print axioms R1Z.PV_Inv_IM31Array.update
#print axioms R1Z.PV_Inv_IM31Array.previous_val
#print axioms R1Z.PV_Inv_IM31Array.predecessor_value
#print axioms R1Z.PV_Inv_InterpolationLoop.preserves
#print axioms R1Z.PV_Inv_InterpolationLoop.initialized
#print axioms R1Z.PV_Inv_ModelPack.producer
#print axioms R1Z.PV_Inv_ModelPack.consumer
#print axioms R1Z.PV_Inv_NativeCompress.exact_value
#print axioms R1Z.PV_Inv_NativeInverseM.raw_nonzero
#print axioms R1Z.PV_Inv_NativeInverseM.inverse_safe
#print axioms R1Z.PV_Inv_NativeNormQ.norm_operand
#print axioms R1Z.PV_Inv_NativePackedTests.packing_tests
#print axioms R1Z.PV_Inv_NativeRegistry.producer
#print axioms R1Z.PV_Inv_Norm.norm_zero
#print axioms R1Z.PV_Inv_Norm.norm_nonzero
#print axioms R1Z.PV_Inv_Pack.put_safe
#print axioms R1Z.PV_Inv_Pack.step_safe
#print axioms R1Z.PV_Inv_Pack.empty_safe
#print axioms R1Z.PV_Inv_PackOperands.reached_nonzero
#print axioms R1Z.PV_Inv_PackOperands.packed_nonzero
#print axioms R1Z.PV_Inv_PoleMass.contained
#print axioms R1Z.PV_Inv_PoleMass.mass
#print axioms R1Z.PV_Inv_RawCanonical.reached_canonical
#print axioms R1Z.PV_Inv_RawInvoke.reached_good
#print axioms R1Z.PV_Inv_RawInvoke.reached_origin
#print axioms R1Z.PV_Inv_RawMapRun.run_map
#print axioms R1Z.PV_Inv_RawNative.packed_nonzero
#print axioms R1Z.PV_Inv_RawSchedule.run_shape
#print axioms R1Z.PV_Inv_RawSchedule.same_weights
#print axioms R1Z.PV_Inv_RawU32.zero_value
#print axioms R1Z.PV_Inv_RegistrySlot.producer
#print axioms R1Z.PV_Inv_RegistrySlot.consumer
#print axioms R1Z.PV_Inv_ScanAppend.append
#print axioms R1Z.PV_Inv_ScanAppend.false_sticky
#print axioms R1Z.PV_Inv_ScanAppend.prefix_clear
#print axioms R1Z.PV_Inv_ScanMask.rows_iff
#print axioms R1Z.PV_Inv_Sentinel.zero_reject
#print axioms R1Z.PV_Inv_Sentinel.nonzero_success
#print axioms R1Z.PV_Inv_SourceInverseTrace.success
#print axioms R1Z.PV_Inv_TupleModel.model
#print axioms R1Z.PV_Inv_WordTuple.model
