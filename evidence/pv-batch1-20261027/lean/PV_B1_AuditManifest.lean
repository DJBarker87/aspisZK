import PV_B1_230_Funs
import PV_B1_230_Types
import PV_B1_254_Funs
import PV_B1_254_Types
import PV_B1_258_Funs
import PV_B1_258_Types
import PV_B1_ArrayRead
import PV_B1_Carrier230
import PV_B1_Carrier254
import PV_B1_Carrier258
import PV_B1_CarrierContainers
import PV_B1_CarrierResultRecovery
import PV_B1_CarrierWide
import PV_B1_FieldCM31Total
import PV_B1_FieldCTTotal
import PV_B1_FieldM31Total
import PV_B1_FieldQM31Total
import PV_B1_FieldWideTotal
import PV_B1_HostExternalFuns
import PV_B1_HostExternalTypes
import PV_B1_HostFailureIndependence
import PV_B1_HostNoDivergence
import PV_B1_HostPoleOutcome
import PV_B1_HostPoleTruth
import PV_B1_HostPowersTotal
import PV_B1_HostSumOption
import PV_B1_HostSumOutcome
import PV_B1_HostSumSource
import PV_B1_HostSumValue
import PV_B1_HostTypes
import PV_B1_InspectCore
import PV_B1_Install
import PV_B1_InstallStability
import PV_B1_Loop
import PV_B1_LoopSteps
import PV_B1_MaskCast
import PV_B1_MaskShift
import PV_B1_Orig258_Op258End
import PV_B1_Orig258_Op258Failure
import PV_B1_Orig258_Op258Fold
import PV_B1_Orig258_Op258FoldAll
import PV_B1_Orig258_Op258Frame
import PV_B1_Orig258_Op258Outside
import PV_B1_Orig258_Op258RowLaw
import PV_B1_Orig258_Op258Step
import PV_B1_Orig258_Op258Total
import PV_B1_Orig258_PoleAdvance
import PV_B1_Orig258_PoleBoolean
import PV_B1_Orig258_PoleIndex
import PV_B1_OriginalEqualTotal
import PV_B1_OriginalPowersTotal
import PV_B1_PoleBody
import PV_B1_PoleBridge
import PV_B1_PoleControl
import PV_B1_PoleEqual
import PV_B1_PoleFalseLaw
import PV_B1_PoleInner
import PV_B1_PoleKeep
import PV_B1_PoleLiterals
import PV_B1_PoleMiddle
import PV_B1_PoleOriginal
import PV_B1_PoleOriginalEqual
import PV_B1_PoleOutcome
import PV_B1_PoleRow
import PV_B1_PowersBridge
import PV_B1_PowersControl
import PV_B1_PowersOriginal
import PV_B1_PowersOriginalControl
import PV_B1_PowersOriginalFinite
import PV_B1_PowersTotal
import PV_B1_ReadTotal
import PV_B1_ReferenceInstall
import PV_B1_ReferenceOutcome
import PV_B1_ResultFaithful
import PV_B1_SelectedContract
import PV_B1_Shift31
import PV_B1_SumControl
import PV_B1_SumFold
import PV_B1_SumNative
import PV_B1_SumOriginal
import PV_B1_Transport
import PV_B1_WordZero
open Aeneas Aeneas.Std
-- Frozen dependency closure and standard-axiom audit only.
#print axioms PV_B1_230.aspis_core.field.P
#print axioms PV_B1_230.aspis_core.field.ct.subtract_p
#print axioms PV_B1_230.aspis_core.field.ct.add
#print axioms PV_B1_230.aspis_core.field.M31.add
#print axioms PV_B1_230.aspis_core.field.CM31.add
#print axioms PV_B1_230.aspis_core.field.QM31.ZERO
#print axioms PV_B1_230.aspis_core.field.QM31.add
#print axioms PV_B1_230.TRACE_ROWS
#print axioms PV_B1_230.state_only_copy_helper_sum_loop.body
#print axioms PV_B1_230.state_only_copy_helper_sum_loop
#print axioms PV_B1_230.state_only_copy_helper_sum
#print axioms PV_B1_230.aspis_core.field.M31
#print axioms PV_B1_230.aspis_core.field.CM31
#print axioms PV_B1_230.aspis_core.field.QM31
#print axioms PV_B1_254.aspis_core.field.P
#print axioms PV_B1_254.aspis_core.field.ct.subtract_p
#print axioms PV_B1_254.aspis_core.field.ct.reduce64
#print axioms PV_B1_254.aspis_core.field.ct.add
#print axioms PV_B1_254.aspis_core.field.ct.sub
#print axioms PV_B1_254.aspis_core.field.QM31.ZERO
#print axioms PV_B1_254.aspis_core.field.wide_exact.WideExact.ZERO
#print axioms PV_B1_254.aspis_core.field.QM31.ONE
#print axioms PV_B1_254.aspis_core.field.wide_exact.WideExact.ONE
#print axioms PV_B1_254.aspis_core.field.M31.sub
#print axioms PV_B1_254.aspis_core.field.M31.add
#print axioms PV_B1_254.aspis_core.field.M31.double
#print axioms PV_B1_254.aspis_core.field.mul_by_r
#print axioms PV_B1_254.aspis_core.field.reduce_u64
#print axioms PV_B1_254.aspis_core.field.M31.reduce_u64
#print axioms PV_B1_254.aspis_core.field.M31.mul
#print axioms PV_B1_254.aspis_core.field.CM31.mul
#print axioms PV_B1_254.aspis_core.field.CM31.sub
#print axioms PV_B1_254.aspis_core.field.CM31.add
#print axioms PV_B1_254.aspis_core.field.QM31.mul
#print axioms PV_B1_254.aspis_core.field.QM31.sub
#print axioms PV_B1_254.aspis_core.field.QM31.add
#print axioms PV_B1_254.aspis_core.field.wide_exact.mul_u
#print axioms PV_B1_254.aspis_core.field.wide_exact.WideExact.mul
#print axioms PV_B1_254.powers_loop.body
#print axioms PV_B1_254.powers_loop
#print axioms PV_B1_254.powers
#print axioms PV_B1_254.aspis_core.field.M31
#print axioms PV_B1_254.aspis_core.field.CM31
#print axioms PV_B1_254.aspis_core.field.QM31
#print axioms PV_B1_254.aspis_core.field.wide_exact.WideExact
#print axioms PV_B1_258.equal
#print axioms PV_B1_258.keep_clear
#print axioms PV_B1_258.all_slots_clear_loop0_loop0_loop0.body
#print axioms PV_B1_258.all_slots_clear_loop0_loop0_loop0
#print axioms PV_B1_258.all_slots_clear_loop0_loop0.body
#print axioms PV_B1_258.all_slots_clear_loop0_loop0
#print axioms PV_B1_258.all_slots_clear_loop0.body
#print axioms PV_B1_258.all_slots_clear_loop0
#print axioms PV_B1_258.all_slots_clear
#print axioms PV_B1_258.aspis_core.field.M31
#print axioms PV_B1_258.aspis_core.field.CM31
#print axioms PV_B1_258.aspis_core.field.QM31
#print axioms PV_B1_ArrayRead.read
#print axioms PV_B1_ArrayRead.first
#print axioms PV_B1_ArrayRead.second
#print axioms PV_B1_ArrayRead.slice_read
#print axioms PV_B1_ArrayRead.array_fail
#print axioms PV_B1_Carrier230.from_to
#print axioms PV_B1_Carrier230.to_from
#print axioms PV_B1_Carrier230.injective
#print axioms PV_B1_Carrier254.from_to
#print axioms PV_B1_Carrier254.to_from
#print axioms PV_B1_Carrier254.injective
#print axioms PV_B1_Carrier258.from_to
#print axioms PV_B1_Carrier258.to_from
#print axioms PV_B1_Carrier258.injective
#print axioms PV_B1_CarrierContainers.sum_input
#print axioms PV_B1_CarrierContainers.powers_output
#print axioms PV_B1_CarrierContainers.row_inverse
#print axioms PV_B1_CarrierContainers.pole_input
#print axioms PV_B1_CarrierResultRecovery.wide
#print axioms PV_B1_CarrierResultRecovery.sum
#print axioms PV_B1_CarrierWide.from_to
#print axioms PV_B1_CarrierWide.to_from
#print axioms PV_B1_CarrierWide.injective
#print axioms PV_B1_FieldCM31Total.add
#print axioms PV_B1_FieldCM31Total.sub
#print axioms PV_B1_FieldCM31Total.mul
#print axioms PV_B1_FieldCM31Total.mul_by_r
#print axioms PV_B1_FieldCTTotal.subtract_p
#print axioms PV_B1_FieldCTTotal.reduce64
#print axioms PV_B1_FieldCTTotal.add
#print axioms PV_B1_FieldCTTotal.sub
#print axioms PV_B1_FieldM31Total.add
#print axioms PV_B1_FieldM31Total.sub
#print axioms PV_B1_FieldM31Total.double
#print axioms PV_B1_FieldM31Total.reduce64
#print axioms PV_B1_FieldM31Total.mul
#print axioms PV_B1_FieldQM31Total.add
#print axioms PV_B1_FieldQM31Total.sub
#print axioms PV_B1_FieldQM31Total.mul
#print axioms PV_B1_FieldWideTotal.mul_u
#print axioms PV_B1_FieldWideTotal.mul
#print axioms PV_B1_Host.ExternalFuns
#print axioms PV_B1_Host.Shared0T.Insts.CoreConvertAsRef.as_ref
#print axioms PV_B1_Host.Slice.Insts.CoreConvertAsRefSlice.as_ref
#print axioms PV_B1_Host.core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq
#print axioms PV_B1_Host.core.mem.take
#print axioms PV_B1_Host.core.mem.drop
#print axioms PV_B1_Host.core.option.Option.is_some_and
#print axioms PV_B1_Host.core.option.Option.as_ref
#print axioms PV_B1_Host.core.option.Option.ok_or
#print axioms PV_B1_Host.core.option.Option.Insts.CoreCmpPartialEqOption.eq
#print axioms PV_B1_Host.core.option.Option.Insts.CoreOpsTry_traitTry.branch
#print axioms PV_B1_Host.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
#print axioms PV_B1_Host.core.result.Result.map
#print axioms PV_B1_Host.core.result.Result.map_err
#print axioms PV_B1_Host.core.sync.atomic.compiler_fence
#print axioms PV_B1_Host.std.fs.File.open
#print axioms PV_B1_Host.std.fs.File.sync_all
#print axioms PV_B1_Host.std.io.Write.write_all.default
#print axioms PV_B1_Host.std.fs.File.Insts.StdIoWrite.flush
#print axioms PV_B1_Host.std.fs.File.Insts.StdIoWrite.write
#print axioms PV_B1_Host.std.fs.OpenOptions.new
#print axioms PV_B1_Host.std.fs.OpenOptions.write
#print axioms PV_B1_Host.std.fs.OpenOptions.create_new
#print axioms PV_B1_Host.std.fs.OpenOptions.open
#print axioms PV_B1_Host.std.io.error.Error.kind
#print axioms PV_B1_Host.std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode
#print axioms PV_B1_Host.std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref
#print axioms PV_B1_Host.std.path.Path.join
#print axioms PV_B1_Host.std.path.Path.Insts.CoreConvertAsRefPath.as_ref
#print axioms PV_B1_Host.alloc.string.String.Insts.CoreConvertAsRefPath.as_ref
#print axioms PV_B1_Host.std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref
#print axioms PV_B1_Host.alloc.string.String.with_capacity
#print axioms PV_B1_Host.alloc.string.String.push_str
#print axioms PV_B1_Host.alloc.vec.Vec.try_reserve_exact
#print axioms PV_B1_Host.alloc.vec.Vec.pop
#print axioms PV_B1_Host.alloc.vec.Vec.is_empty
#print axioms PV_B1_Host.alloc.vec.Vec.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.Array.Insts.CoreConvertTryFromVecVec.try_from
#print axioms PV_B1_Host.aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
#print axioms PV_B1_Host.aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.ZERO
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.impl.c0
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.impl.c1
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.from_qm31
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.add
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.mul
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.mul_qm31
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.to_limbs
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.from_le_bytes
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.to_le_bytes
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.mul_m31
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
#print axioms PV_B1_Host.aspis_core.field.M31.ZERO
#print axioms PV_B1_Host.aspis_core.field.M31.ONE
#print axioms PV_B1_Host.aspis_core.field.M31.mul
#print axioms PV_B1_Host.aspis_core.field.M31.double
#print axioms PV_B1_Host.aspis_core.field.M31.inv
#print axioms PV_B1_Host.aspis_core.field.CM31.new
#print axioms PV_B1_Host.aspis_core.field.CM31.from_m31
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
#print axioms PV_B1_Host.aspis_core.field.QM31.ZERO
#print axioms PV_B1_Host.aspis_core.field.QM31.ONE
#print axioms PV_B1_Host.aspis_core.field.QM31.from_cm31
#print axioms PV_B1_Host.aspis_core.field.QM31.add
#print axioms PV_B1_Host.aspis_core.field.QM31.sub
#print axioms PV_B1_Host.aspis_core.field.QM31.mul
#print axioms PV_B1_Host.aspis_core.field.QM31.mul_m31
#print axioms PV_B1_Host.aspis_core.field.QM31.from_le_bytes
#print axioms PV_B1_Host.aspis_core.field.QM31.write_le_bytes
#print axioms PV_B1_Host.aspis_core.field.M31.add
#print axioms PV_B1_Host.aspis_core.field.M31.sub
#print axioms PV_B1_Host.aspis_core.r0.domain.FibreIndex.new
#print axioms PV_B1_Host.aspis_core.r0.domain.FibreIndex.get
#print axioms PV_B1_Host.aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.aspis_core.r0.domain.fibre_point
#print axioms PV_B1_Host.aspis_core.r0.encoder.eval_message
#print axioms PV_B1_Host.aspis_core.r0.fold.phi_inverse
#print axioms PV_B1_Host.aspis_core.r0.heap.filled
#print axioms PV_B1_Host.aspis_core.r0.merkle.C1_TAG
#print axioms PV_B1_Host.aspis_core.r0.merkle.C2_TAG
#print axioms PV_B1_Host.aspis_core.r0.merkle.leaf
#print axioms PV_B1_Host.aspis_core.r0.Error.Insts.CoreFmtDebug.fmt
#print axioms PV_B1_Host.aspis_core.r0.opening.LANES
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ZERO
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ZERO
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ZERO
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ONE
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ONE
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ONE
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.add
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.add
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.add
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.sub
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.sub
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.sub
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.neg
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.mul
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.mul
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.mul
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv
#print axioms PV_B1_Host.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv
#print axioms PV_B1_Host.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
#print axioms PV_B1_Host.aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
#print axioms PV_B1_Host.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
#print axioms PV_B1_Host.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
#print axioms PV_B1_Host.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq
#print axioms PV_B1_Host.aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
#print axioms PV_B1_Host.aspis_core.state_only_hiding.StateOnlyHidingContext.encode
#print axioms PV_B1_Host.aspis_core.state_only_hiding.state_only_selected_mask_value
#print axioms PV_B1_Host.aspis_core.state_only_prefix.r0.statement_points
#print axioms PV_B1_Host.aspis_core.state_only_private_merkle.private_leaf_hash
#print axioms PV_B1_Host.aspis_core.state_only_sumcheck.state_only_boundary_sum
#print axioms PV_B1_Host.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
#print axioms PV_B1_Host.Array.Insts.ZeroizeZeroize.zeroize
#print axioms PV_B1_Host.zeroize.Zeroize.Blanket.zeroize
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.volatile_clear_cell
#print axioms PV_B1_Host.zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut
#print axioms PV_B1_Host.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
#print axioms PV_B1_Host.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
#print axioms PV_B1_Host.zeroize.Zeroizing.new
#print axioms PV_B1_Host.getrandom.fill
#print axioms PV_B1_Host.zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize
#print axioms PV_B1_Host.zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar.private_cmp
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess.private_cmp
#print axioms PV_B1_Host.typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp
#print axioms PV_B1_Host.typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output.private_cmp
#print axioms PV_B1_Host.typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp
#print axioms PV_B1_Host.typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output.compare
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_isize
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i64
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i32
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i16
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i8
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_usize
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u64
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u32
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u16
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u8
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.ISIZE
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I64
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I32
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I16
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I8
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.USIZE
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U64
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U32
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U16
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U8
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.typenum.uint.UInt.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_isize
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i64
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i32
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i16
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i8
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_usize
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u64
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u32
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u16
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u8
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.ISIZE
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I64
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I32
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I16
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I8
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.USIZE
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U64
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U32
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U16
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U8
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.typenum.uint.UTerm.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.typenum.type_operators.IsLessOrEqual.Blanket.is_less_or_equal
#print axioms PV_B1_Host.typenum.type_operators.IsLess.Blanket.is_less
#print axioms PV_B1_Host.typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket.is_less_or_equal_private
#print axioms PV_B1_Host.typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_bool
#print axioms PV_B1_Host.typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_u8
#print axioms PV_B1_Host.typenum.bit.B1.Insts.TypenumMarker_traitsBit.new
#print axioms PV_B1_Host.typenum.bit.B1.Insts.TypenumMarker_traitsBit.BOOL
#print axioms PV_B1_Host.typenum.bit.B1.Insts.TypenumMarker_traitsBit.U8
#print axioms PV_B1_Host.typenum.bit.B1.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.typenum.bit.B1.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.typenum.private.IsLessPrivateABLessB1.Blanket.is_less_private
#print axioms PV_B1_Host.typenum.Equal.Insts.TypenumMarker_traitsOrd.to_ordering
#print axioms PV_B1_Host.typenum.Greater.Insts.TypenumMarker_traitsOrd.to_ordering
#print axioms PV_B1_Host.typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_bool
#print axioms PV_B1_Host.typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_u8
#print axioms PV_B1_Host.typenum.bit.B0.Insts.TypenumMarker_traitsBit.new
#print axioms PV_B1_Host.typenum.bit.B0.Insts.TypenumMarker_traitsBit.BOOL
#print axioms PV_B1_Host.typenum.bit.B0.Insts.TypenumMarker_traitsBit.U8
#print axioms PV_B1_Host.typenum.bit.B0.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.typenum.bit.B0.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core
#print axioms PV_B1_Host.sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.new
#print axioms PV_B1_Host.sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.TRUNC_SIDE
#print axioms PV_B1_Host.sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks
#print axioms PV_B1_Host.block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks
#print axioms PV_B1_Host.block_buffer.Eager.Insts.Block_bufferSealedSealed.invariant
#print axioms PV_B1_Host.ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0.from
#print axioms PV_B1_Host.digest.digest.Digest.Blanket.finalize
#print axioms PV_B1_Host.digest.digest.Digest.Blanket.update
#print axioms PV_B1_Host.digest.digest.Digest.Blanket.new
#print axioms PV_B1_Host.digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into
#print axioms PV_B1_Host.digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update
#print axioms PV_B1_Host.digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core
#print axioms PV_B1_Host.digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiUpdateCore.update_blocks
#print axioms PV_B1_Host.block_buffer.Eager.Insts.CoreDefaultDefault.default
#print axioms PV_B1_Host.aspis_statement.constraints_v4.multilinear_evaluate_qm31
#print axioms PV_B1_Host.aspis_statement.logup.compress_tagged_tuple
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq
#print axioms PV_B1_Host.aspis_statement.state_only_semantic.state_only_copy_helper_sum
#print axioms PV_B1_Host.aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
#print axioms PV_B1_Host.aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check
#print axioms PV_B1_Host.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
#print axioms PV_B1_Host.transport.Variant.tag
#print axioms PV_B1_Host.multiproof.LEAF_BITS
#print axioms PV_B1_Host.multiproof.MAX_BATCH
#print axioms PV_B1_Host.compact.SLOT_NODES
#print axioms PV_B1_Host.host_commitment.clear_private_salt
#print axioms PV_B1_Host.r1_wire.CLAIMS
#print axioms PV_B1_Host.r1_wire.LANES
#print axioms PV_B1_Host.compact.LOGICAL_SEMANTIC
#print axioms PV_B1_Host.compact.PROOF_BYTES
#print axioms PV_B1_Host.compact.OFF_NODES
#print axioms PV_B1_Host.compact.OFF_OPENINGS
#print axioms PV_B1_Host.compact.MAGIC
#print axioms PV_B1_Host.multiproof.binary_parent
#print axioms PV_B1_Host.trace.value
#print axioms PV_B1_Host.sampler.qm31_sample
#print axioms PV_B1_Host.sampler.gamma_sample
#print axioms PV_B1_Host.sampler.ordinary_sample
#print axioms PV_B1_Host.weights.Weights.materialize
#print axioms PV_B1_Host.weights.Weights.new
#print axioms PV_B1_Host.weights.Weights.raw
#print axioms PV_B1_Host.weights.powers
#print axioms PV_B1_Host.transport.Variant.coefficients
#print axioms PV_B1_Host.r1_wire.Error.Insts.CoreCmpPartialEqError.eq
#print axioms PV_B1_Host.host_work.map
#print axioms PV_B1_Host.ct_pole.all_slots_clear
#print axioms PV_B1_Host.sampler.circle_sample
#print axioms PV_B1_Host.r1_wire.DOMAIN
#print axioms PV_B1_Host.std.fs.File.Insts.StdIoWrite.write_all
#print axioms PV_B1_Host.ExternalTypes
#print axioms PV_B1_Host.std.fs.File
#print axioms PV_B1_Host.std.fs.OpenOptions
#print axioms PV_B1_Host.std.path.Path
#print axioms PV_B1_Host.std.io.error.Error
#print axioms PV_B1_Host.std.path.PathBuf
#print axioms PV_B1_Host.alloc.collections.TryReserveError
#print axioms PV_B1_Host.aspis_core.state_only_prefix.r0.Error
#print axioms PV_B1_Host.getrandom.error.Error
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
#print axioms PV_B1_Host.typenum.uint.UInt
#print axioms PV_B1_Host.sha2.core_api.Sha256VarCore
#print axioms PV_B1_Host.generic_array.GenericArray
#print axioms PV_B1_Host.generic_array.GenericArrayImplOdd
#print axioms PV_B1_Host.generic_array.GenericArrayImplEven
#print axioms PV_B1_Host.block_buffer.BlockBuffer
#print axioms PV_B1_Host.digest.core_api.wrapper.CoreWrapper
#print axioms PV_B1_Host.digest.core_api.ct_variable.CtVariableCoreWrapper
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1
#print axioms PV_B1_Host.weights.Weights
#print axioms PV_B1_Host.F64
#print axioms PV_B1_Host.core.fmt.Formatter
#print axioms PV_B1_Host.core.fmt.Debug
#print axioms PV_B1_HostFailureIndependence.same_length
#print axioms PV_B1_HostNoDivergence.sum
#print axioms PV_B1_HostNoDivergence.powers
#print axioms PV_B1_HostNoDivergence.pole
#print axioms PV_B1_HostPoleOutcome.length
#print axioms PV_B1_HostPoleOutcome.total
#print axioms PV_B1_HostPoleOutcome.failure_iff
#print axioms PV_B1_HostPoleTruth.truth
#print axioms PV_B1_HostPoleTruth.falsity
#print axioms PV_B1_HostPowersTotal.total
#print axioms PV_B1_HostSumOption.none_iff
#print axioms PV_B1_HostSumOption.some_iff
#print axioms PV_B1_HostSumOutcome.wrong_length
#print axioms PV_B1_HostSumOutcome.exact_length
#print axioms PV_B1_HostSumOutcome.total
#print axioms PV_B1_HostSumSource.original_transport
#print axioms PV_B1_HostSumSource.op230_source
#print axioms PV_B1_HostSumValue.to_zero
#print axioms PV_B1_HostSumValue.to_add
#print axioms PV_B1_HostSumValue.fold
#print axioms PV_B1_Host.core.io.error.ErrorKind
#print axioms PV_B1_Host.core.io.error.ErrorKind.read_discriminant
#print axioms PV_B1_Host.core.sync.atomic.Ordering
#print axioms PV_B1_Host.core.sync.atomic.Ordering.read_discriminant
#print axioms PV_B1_Host.std.io.Write
#print axioms PV_B1_Host.aspis_core.field.M31
#print axioms PV_B1_Host.aspis_core.field.CM31
#print axioms PV_B1_Host.aspis_core.field.QM31
#print axioms PV_B1_Host.aspis_core.circle.SecureCirclePoint
#print axioms PV_B1_Host.aspis_core.digest.Digest32
#print axioms PV_B1_Host.aspis_core.digest.LegacyHashFn
#print axioms PV_B1_Host.aspis_core.field.wide_exact.WideExact
#print axioms PV_B1_Host.aspis_core.r0.domain.FibreIndex
#print axioms PV_B1_Host.aspis_core.r0.Error
#print axioms PV_B1_Host.aspis_core.r0.Error.read_discriminant
#print axioms PV_B1_Host.aspis_core.r0.domain.Point
#print axioms PV_B1_Host.aspis_core.r0.scalar.CodeField
#print axioms PV_B1_Host.aspis_core.r0.wire.FibreOpening
#print axioms PV_B1_Host.aspis_core.r0_transcript.CircleRow
#print axioms PV_B1_Host.aspis_core.r0_transcript.CircleRow.read_discriminant
#print axioms PV_B1_Host.aspis_core.state_only_hiding.StateOnlyHidingContext
#print axioms PV_B1_Host.aspis_core.state_only_prefix.r0.Challenges
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.read_discriminant
#print axioms PV_B1_Host.zeroize.Zeroizing
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
#print axioms PV_B1_Host.zeroize.Zeroize
#print axioms PV_B1_Host.zeroize.DefaultIsZeroes
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.SensitiveQm31Vec
#print axioms PV_B1_Host.aspis_statement.trace_v4.TraceCell
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.StateOnlyMaskNonceStore
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.StateOnlyMaskBuildError
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.StateOnlyMaskBuildError.read_discriminant
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.SeedExpander
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.StateOnlyMaskMaterial
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows.closure_1
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows.closure
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.PreReservedNonce
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.Profile21SourceExpander
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d.closure
#print axioms PV_B1_Host.aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
#print axioms PV_B1_Host.typenum.uint.UTerm
#print axioms PV_B1_Host.typenum.sealed.Sealed
#print axioms PV_B1_Host.typenum.marker_traits.Ord
#print axioms PV_B1_Host.typenum.private.PrivateCmp
#print axioms PV_B1_Host.typenum.marker_traits.Unsigned
#print axioms PV_B1_Host.typenum.marker_traits.Bit
#print axioms PV_B1_Host.typenum.Less
#print axioms PV_B1_Host.typenum.Greater
#print axioms PV_B1_Host.typenum.bit.B1
#print axioms PV_B1_Host.typenum.bit.B0
#print axioms PV_B1_Host.typenum.private.InternalMarker
#print axioms PV_B1_Host.typenum.Equal
#print axioms PV_B1_Host.typenum.type_operators.Cmp
#print axioms PV_B1_Host.typenum.private.IsLessOrEqualPrivate
#print axioms PV_B1_Host.typenum.type_operators.IsLessOrEqual
#print axioms PV_B1_Host.typenum.private.IsLessPrivate
#print axioms PV_B1_Host.typenum.type_operators.IsLess
#print axioms PV_B1_Host.typenum.marker_traits.NonZero
#print axioms PV_B1_Host.block_buffer.Eager
#print axioms PV_B1_Host.digest.InvalidOutputSize
#print axioms PV_B1_Host.digest.core_api.TruncSide
#print axioms PV_B1_Host.digest.core_api.TruncSide.read_discriminant
#print axioms PV_B1_Host.generic_array.ArrayLength
#print axioms PV_B1_Host.crypto_common.OutputSizeUser
#print axioms PV_B1_Host.crypto_common.BlockSizeUser
#print axioms PV_B1_Host.digest.core_api.UpdateCore
#print axioms PV_B1_Host.block_buffer.sealed.Sealed
#print axioms PV_B1_Host.block_buffer.BufferKind
#print axioms PV_B1_Host.digest.core_api.BufferKindUser
#print axioms PV_B1_Host.digest.core_api.VariableOutputCore
#print axioms PV_B1_Host.digest.digest.HashMarker
#print axioms PV_B1_Host.digest.Update
#print axioms PV_B1_Host.digest.FixedOutput
#print axioms PV_B1_Host.digest.core_api.FixedOutputCore
#print axioms PV_B1_Host.sha2.OidSha256
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.AppliedStateOnlyMasks
#print axioms PV_B1_Host.aspis_statement.state_only_trace.StateOnlyTraceFoundation
#print axioms PV_B1_Host.aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceBankV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceBankV1.read_discriminant
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceCellV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1.read_discriminant
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1
#print axioms PV_B1_Host.aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1
#print axioms PV_B1_Host.aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges
#print axioms PV_B1_Host.aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes
#print axioms PV_B1_Host.verifier.Error
#print axioms PV_B1_Host.verifier.Error.read_discriminant
#print axioms PV_B1_Host.transport.Variant
#print axioms PV_B1_Host.transport.Variant.read_discriminant
#print axioms PV_B1_Host.prover.MaskedFixtureAudit
#print axioms PV_B1_Host.prover.RetriedProof
#print axioms PV_B1_Host.r1_wire.Error
#print axioms PV_B1_Host.r1_wire.Error.read_discriminant
#print axioms PV_B1_Host.host_commitment.PrivateSalts
#print axioms PV_B1_Host.host_tree.BinaryTree
#print axioms PV_B1_Host.host_commitment.Word
#print axioms PV_B1_Host.host_commitment.Word.read_discriminant
#print axioms PV_B1_Host.host_commitment.CommitmentTime
#print axioms PV_B1_Host.host_commitment.CommitmentTime.read_discriminant
#print axioms PV_B1_Host.host_commitment.Commitment
#print axioms PV_B1_Host.prover.publish_compact.closure_1
#print axioms PV_B1_Host.compact.CodecError
#print axioms PV_B1_Host.compact.CodecError.read_discriminant
#print axioms PV_B1_Host.prover.publish_compact.closure
#print axioms PV_B1_Host.host_commitment.EncodingDomain
#print axioms PV_B1_Host.prover.Backend
#print axioms PV_B1_Host.prover.Publication
#print axioms PV_B1_Host.host_transcript.Transcript
#print axioms PV_B1_Host.host_wire.SemanticTranscript
#print axioms PV_B1_Host.host_semantic.BuiltSemantics
#print axioms PV_B1_Host.prover.PreparedOpening
#print axioms PV_B1_Host.prover.prepare_opening.closure
#print axioms PV_B1_Host.prover.derive_private_salt_step.closure
#print axioms PV_B1_Host.prover.derive_private_salts.closure
#print axioms PV_B1_Host.prover.prove_masked_with_attempt.closure_3
#print axioms PV_B1_Host.prover.prove_masked_with_attempt.closure_2
#print axioms PV_B1_Host.prover.prove_masked_with_attempt.closure_1
#print axioms PV_B1_Host.prover.prove_masked_with_attempt.closure
#print axioms PV_B1_Host.prover.CommitmentsBackend.c2.closure
#print axioms PV_B1_Host.host_commitment.EncodingDomain.encode.closure
#print axioms PV_B1_Host.host_commitment.encode_commitment_words.closure_1
#print axioms PV_B1_Host.host_commitment.encode_commitment_words.closure
#print axioms PV_B1_Host.host_commitment.Commitment.build.closure
#print axioms PV_B1_Host.prover.CommitmentsBackend.c1.closure
#print axioms PV_B1_Host.host_semantic.Commitments
#print axioms PV_B1_Host.host_semantic.lean_copy_row_values.closure
#print axioms PV_B1_Host.host_semantic.no_pole.closure
#print axioms PV_B1_Host.host_semantic.build_with_material.closure.closure
#print axioms PV_B1_Host.host_semantic.build_with_material.closure
#print axioms PV_B1_Host.host_wire.SemanticTranscript.new.closure
#print axioms PV_B1_Host.host_sumcheck.Oracle
#print axioms PV_B1_Host.host_sumcheck.prove_sumcheck_round.closure
#print axioms PV_B1_Host.host_semantic.OracleSemanticOracle.evaluate.closure
#print axioms PV_B1_Host.host_semantic.SemanticOracle
#print axioms PV_B1_Host.host_semantic.build_with_helper_mode.closure_1
#print axioms PV_B1_Host.host_semantic.build_with_helper_mode.closure
#print axioms PV_B1_Host.host_commitment.EncodingDomain.new.closure
#print axioms PV_B1_Host.prover.prove_masked_attempt.closure
#print axioms PV_B1_Host.RealR1_client.prove_for_proof_accounts.closure.closure
#print axioms PV_B1_Host.RealR1_client.prove_for_proof_accounts.closure
#print axioms core.num.U32.wrapping_add
#print axioms core.num.U32.wrapping_sub
#print axioms PV_B1_Install.op230_source
#print axioms PV_B1_Install.op254_source
#print axioms PV_B1_Install.op258_source
#print axioms PV_B1_Install.compressor_preserved
#print axioms PV_B1_Install.wide_primitive_preserved
#print axioms PV_B1_InstallStability.idempotent
#print axioms PV_B1_InstallStability.old_callbacks_removed
#print axioms PV_B1_InstallStability.op134_preserved
#print axioms PV_B1_InstallStability.op259_preserved
#print axioms PV_B1_Loop.bind
#print axioms PV_B1_LoopSteps.done_step
#print axioms PV_B1_LoopSteps.continue_step
#print axioms PV_B1_LoopSteps.fail_step
#print axioms PV_B1_MaskCast.low_value
#print axioms PV_B1_MaskCast.low_bound
#print axioms PV_B1_MaskCast.cast_value
#print axioms PV_B1_MaskCast.literal_four
#print axioms PV_B1_MaskCast.cast_nonfailure
#print axioms PV_B1_MaskShift.four_mod
#print axioms PV_B1_MaskShift.block_value
#print axioms PV_B1_MaskShift.in_bounds
#print axioms PV_B1_MaskShift.out_of_bounds
#print axioms PV_B1_MaskShift.bit_value
#print axioms PV_B1_MaskShift.row_shift_nonfailure
#print axioms PV_B1_MaskShift.bit_shift_nonfailure
#print axioms PV_B1_Orig258_Op258End.body_done
#print axioms PV_B1_Orig258_Op258Failure.body
#print axioms PV_B1_Orig258_Op258Failure.loop
#print axioms PV_B1_Orig258_Op258Fold.body_frame
#print axioms PV_B1_Orig258_Op258Fold.loop_scan
#print axioms PV_B1_Orig258_Op258Fold.source_scan
#print axioms PV_B1_Orig258_Op258FoldAll.scan_truth
#print axioms PV_B1_Orig258_Op258FoldAll.source_truth
#print axioms PV_B1_Orig258_Op258FoldAll.all_inputs
#print axioms PV_B1_Orig258_Op258Frame.false_step
#print axioms PV_B1_Orig258_Op258Frame.step_frame
#print axioms PV_B1_Orig258_Op258Outside.loop_failure
#print axioms PV_B1_Orig258_Op258Outside.source_failure
#print axioms PV_B1_Orig258_Op258RowLaw.clearRow_iff
#print axioms PV_B1_Orig258_Op258RowLaw.body
#print axioms PV_B1_Orig258_Op258Step.total
#print axioms PV_B1_Orig258_Op258Total.loop_total
#print axioms PV_B1_Orig258_Op258Total.source_total
#print axioms PV_B1_Orig258_PoleAdvance.append
#print axioms PV_B1_Orig258_PoleAdvance.value
#print axioms PV_B1_Orig258_PoleAdvance.from_zero
#print axioms PV_B1_Orig258_PoleBoolean.row_value
#print axioms PV_B1_Orig258_PoleBoolean.inactive
#print axioms PV_B1_Orig258_PoleBoolean.absorbing
#print axioms PV_B1_Orig258_PoleBoolean.clear_iff
#print axioms PV_B1_Orig258_PoleIndex.slice_length
#print axioms PV_B1_Orig258_PoleIndex.slice_read
#print axioms PV_B1_Orig258_PoleIndex.increment
#print axioms PV_B1_OriginalEqualTotal.total
#print axioms PV_B1_OriginalPowersTotal.total
#print axioms PV_B1_OriginalPowersTotal.no_error
#print axioms PV_B1_PoleBody.source
#print axioms PV_B1_PoleBody.original
#print axioms PV_B1_PoleBridge.body
#print axioms PV_B1_PoleBridge.loop_result
#print axioms PV_B1_PoleBridge.op258_source
#print axioms PV_B1_PoleControl.source_unfold
#print axioms PV_B1_PoleControl.dispatch_congr
#print axioms PV_B1_PoleControl.loop_finite
#print axioms PV_B1_PoleControl.op258_source
#print axioms PV_B1_PoleEqual.source_comm
#print axioms PV_B1_PoleEqual.source_self
#print axioms PV_B1_PoleEqual.zero_symmetric
#print axioms PV_B1_PoleEqual.same_words
#print axioms PV_B1_PoleEqual.source
#print axioms PV_B1_PoleEqual.zero
#print axioms PV_B1_PoleFalseLaw.false_iff
#print axioms PV_B1_PoleInner.source_unfold
#print axioms PV_B1_PoleInner.stop
#print axioms PV_B1_PoleInner.one
#print axioms PV_B1_PoleInner.source
#print axioms PV_B1_PoleKeep.equal_source
#print axioms PV_B1_PoleKeep.source
#print axioms PV_B1_PoleKeep.inactive
#print axioms PV_B1_PoleKeep.absorbing
#print axioms PV_B1_PoleLiterals.zero
#print axioms PV_B1_PoleLiterals.one
#print axioms PV_B1_PoleMiddle.source_unfold
#print axioms PV_B1_PoleMiddle.stop
#print axioms PV_B1_PoleMiddle.one
#print axioms PV_B1_PoleMiddle.source
#print axioms PV_B1_PoleOriginal.reference.equal
#print axioms PV_B1_PoleOriginal.reference.all_slots_clear_loop.body
#print axioms PV_B1_PoleOriginal.reference.all_slots_clear_loop
#print axioms PV_B1_PoleOriginal.reference.all_slots_clear
#print axioms PV_B1_PoleOriginalEqual.source
#print axioms PV_B1_PoleOutcome.total
#print axioms PV_B1_PoleOutcome.oversized
#print axioms PV_B1_PoleOutcome.classified
#print axioms PV_B1_PoleOutcome.never_diverges
#print axioms PV_B1_PoleOutcome.failure_iff
#print axioms PV_B1_PoleOutcome.false_still_fails
#print axioms PV_B1_PoleOutcome.truth_iff
#print axioms PV_B1_PoleOutcome.failure_same_length
#print axioms PV_B1_PoleRow.side_value
#print axioms PV_B1_PoleRow.source
#print axioms PV_B1_PowersBridge.step
#print axioms PV_B1_PowersBridge.finite
#print axioms PV_B1_PowersBridge.op254_copy_equal_original
#print axioms PV_B1_PowersControl.source_unfold
#print axioms PV_B1_PowersControl.dispatch_congr
#print axioms PV_B1_PowersControl.loop_finite
#print axioms PV_B1_PowersControl.op254_source
#print axioms PV_B1_PowersOriginal.aspis_core.field.wide_exact.WideExact.ZERO
#print axioms PV_B1_PowersOriginal.aspis_core.field.wide_exact.WideExact.ONE
#print axioms PV_B1_PowersOriginal.aspis_core.field.wide_exact.WideExact.mul
#print axioms PV_B1_PowersOriginal.weights.powers_loop.body
#print axioms PV_B1_PowersOriginal.weights.powers_loop
#print axioms PV_B1_PowersOriginal.weights.powers
#print axioms PV_B1_PowersOriginalControl.source_unfold
#print axioms PV_B1_PowersOriginalControl.dispatch_congr
#print axioms PV_B1_PowersOriginalFinite.loop_finite
#print axioms PV_B1_PowersOriginalFinite.powers_finite
#print axioms PV_B1_PowersTotal.finite_total
#print axioms PV_B1_PowersTotal.total
#print axioms PV_B1_ReadTotal.read_total
#print axioms PV_B1_ReadTotal.bind_total
#print axioms PV_B1_ReferenceInstall.source_eq
#print axioms PV_B1_ReferenceInstall.context_result
#print axioms PV_B1_ReferenceOutcome.sum_total
#print axioms PV_B1_ReferenceOutcome.powers_total
#print axioms PV_B1_ReferenceOutcome.pole_failure
#print axioms PV_B1_ResultFaithful.injective
#print axioms PV_B1_ResultFaithful.failure_iff
#print axioms PV_B1_ResultFaithful.divergence_iff
#print axioms PV_B1_SelectedContract.source_contract
#print axioms PV_B1_Shift31.literal
#print axioms PV_B1_Shift31.nonfailure
#print axioms PV_B1_Shift31.value
#print axioms PV_B1_SumControl.source_unfold
#print axioms PV_B1_SumControl.dispatch_congr
#print axioms PV_B1_SumControl.loop_finite
#print axioms PV_B1_SumControl.op230_source
#print axioms PV_B1_SumFold.read
#print axioms PV_B1_SumFold.step
#print axioms PV_B1_SumFold.finite
#print axioms PV_B1_SumFold.op230_source
#print axioms PV_B1_SumNative.limb_source
#print axioms PV_B1_SumNative.add_source
#print axioms PV_B1_SumNative.fold_source
#print axioms PV_B1_SumNative.op230_source
#print axioms PV_B1_SumOriginal.op230_source
#print axioms PV_B1_SumOriginal.wrong_length
#print axioms PV_B1_SumOriginal.exact_length
#print axioms PV_B1_Transport.result_bind
#print axioms PV_B1_Transport.result_comp
#print axioms PV_B1_Transport.result_identity
#print axioms PV_B1_Transport.result_roundtrip
#print axioms PV_B1_Transport.array_index
#print axioms PV_B1_Transport.slice_index
#print axioms PV_B1_Transport.slice_length
#print axioms PV_B1_Transport.array_set
#print axioms PV_B1_Transport.array_repeat
#print axioms PV_B1_Transport.array_roundtrip
#print axioms PV_B1_Transport.slice_roundtrip
#print axioms PV_B1_WordZero.xor_self
#print axioms PV_B1_WordZero.four_or_zero
#print axioms PV_B1_WordZero.or_zero
#print axioms PV_B1_WordZero.xor_zero
