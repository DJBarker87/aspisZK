import R1Z.PV_Inv_ChargeRules
import R1Z.PV_Inv_CircleImage
import R1Z.PV_Inv_CircleSubfield
import R1Z.PV_Inv_Compression
import R1Z.PV_Inv_ConstantTrace
import R1Z.PV_Inv_GlobalNative
import R1Z.PV_Inv_GlobalPairs
import R1Z.PV_Inv_GlobalSafety
import R1Z.PV_Inv_GlobalSlots
import R1Z.PV_Inv_IBasisPolynomial
import R1Z.PV_Inv_IInterpolationFactors
import R1Z.PV_Inv_IInterpolationInitial
import R1Z.PV_Inv_IInterpolationSchedule
import R1Z.PV_Inv_Interpolation
import R1Z.PV_Inv_InterpolationSource
import R1Z.PV_Inv_ModelRow
import R1Z.PV_Inv_NativeDenominator
import R1Z.PV_Inv_NativeNormC
import R1Z.PV_Inv_NativePackScan
import R1Z.PV_Inv_NativeQ
import R1Z.PV_Inv_NativeScalar
import R1Z.PV_Inv_OperandPrefix
import R1Z.PV_Inv_PackList
import R1Z.PV_Inv_Pivot
import R1Z.PV_Inv_PoleUnion
import R1Z.PV_Inv_RawFailure
import R1Z.PV_Inv_RawMap
import R1Z.PV_Inv_RawMembership
import R1Z.PV_Inv_RawRun
import R1Z.PV_Inv_RawSlots
import R1Z.PV_Inv_RegistryNoPole
import R1Z.PV_Inv_Scan
import R1Z.PV_Inv_ScanCost
import R1Z.PV_Inv_ScanPack
import R1Z.PV_Inv_SourceBranch
import R1Z.PV_Inv_SourceTests
import R1Z.PV_Inv_UniqueSlot
import R1Z.PV_Inv_ZeroTraceLimit

/-! Focused final dependency/import and accepted-axioms audit. Not a frozen release replay. -/
#print axioms R1Z.PV_Inv_ChargeRules.already_charged
#print axioms R1Z.PV_Inv_ChargeRules.no_double_charge
#print axioms R1Z.PV_Inv_CircleImage.on_circle
#print axioms R1Z.PV_Inv_CircleImage.image_avoids_minus_one
#print axioms R1Z.PV_Inv_CircleSubfield.outside_subfield_safe
#print axioms R1Z.PV_Inv_Compression.loop_eq
#print axioms R1Z.PV_Inv_Compression.affine_start
#print axioms R1Z.PV_Inv_ConstantTrace.all_false
#print axioms R1Z.PV_Inv_ConstantTrace.same_schedule
#print axioms R1Z.PV_Inv_GlobalNative.all_reached_tests
#print axioms R1Z.PV_Inv_GlobalPairs.safe_pairs
#print axioms R1Z.PV_Inv_GlobalPairs.build_safe
#print axioms R1Z.PV_Inv_GlobalSafety.run_good
#print axioms R1Z.PV_Inv_GlobalSafety.empty_good
#print axioms R1Z.PV_Inv_GlobalSlots.step_good
#print axioms R1Z.PV_Inv_IBasisPolynomial.multiplication
#print axioms R1Z.PV_Inv_IInterpolationFactors.factors_value
#print axioms R1Z.PV_Inv_IInterpolationInitial.initial_canonical
#print axioms R1Z.PV_Inv_IInterpolationInitial.initial_value
#print axioms R1Z.PV_Inv_IInterpolationInitial.initial_poly
#print axioms R1Z.PV_Inv_IInterpolationInitial.initial_source
#print axioms R1Z.PV_Inv_IInterpolationInitial.prepare_exact
#print axioms R1Z.PV_Inv_IInterpolationSchedule.degree_le
#print axioms R1Z.PV_Inv_IInterpolationSchedule.skipped_degree
#print axioms R1Z.PV_Inv_IInterpolationSchedule.selected_degree
#print axioms R1Z.PV_Inv_IInterpolationSchedule.selected_room
#print axioms R1Z.PV_Inv_IInterpolationSchedule.self_eval
#print axioms R1Z.PV_Inv_IInterpolationSchedule.nat_cast_ne
#print axioms R1Z.PV_Inv_IInterpolationSchedule.denominator_nonzero
#print axioms R1Z.PV_Inv_Interpolation.node_injective
#print axioms R1Z.PV_Inv_Interpolation.denominator_nonzero
#print axioms R1Z.PV_Inv_InterpolationSource.source_inverse_operand
#print axioms R1Z.PV_Inv_ModelRow.producer_clear
#print axioms R1Z.PV_Inv_ModelRow.consumer_clear
#print axioms R1Z.PV_Inv_NativeDenominator.preserves
#print axioms R1Z.PV_Inv_NativeNormC.norm_operand
#print axioms R1Z.PV_Inv_NativePackScan.guarded_packing
#print axioms R1Z.PV_Inv_NativeQ.zero_exact
#print axioms R1Z.PV_Inv_NativeQ.nonzero_test
#print axioms R1Z.PV_Inv_NativeQ.subtract_nonzero
#print axioms R1Z.PV_Inv_NativeScalar.decode_injective
#print axioms R1Z.PV_Inv_NativeScalar.sub_nonzero
#print axioms R1Z.PV_Inv_NativeScalar.mul_nonzero
#print axioms R1Z.PV_Inv_OperandPrefix.take_nonzero
#print axioms R1Z.PV_Inv_OperandPrefix.stopped_prefix
#print axioms R1Z.PV_Inv_OperandPrefix.append_safe
#print axioms R1Z.PV_Inv_PackList.preserves
#print axioms R1Z.PV_Inv_PackList.from_empty
#print axioms R1Z.PV_Inv_Pivot.selected_nonzero
#print axioms R1Z.PV_Inv_Pivot.selected_inverse
#print axioms R1Z.PV_Inv_PoleUnion.eight_attempts
#print axioms R1Z.PV_Inv_RawFailure.failure_iff
#print axioms R1Z.PV_Inv_RawMap.put_map
#print axioms R1Z.PV_Inv_RawMap.step_map
#print axioms R1Z.PV_Inv_RawMembership.reached_origin
#print axioms R1Z.PV_Inv_RawRun.preserves
#print axioms R1Z.PV_Inv_RawRun.empty_good
#print axioms R1Z.PV_Inv_RawSlots.put_good
#print axioms R1Z.PV_Inv_RawSlots.step_good
#print axioms R1Z.PV_Inv_RegistryNoPole.producer
#print axioms R1Z.PV_Inv_RegistryNoPole.consumer
#print axioms R1Z.PV_Inv_Scan.scan_iff
#print axioms R1Z.PV_Inv_Scan.scan_nonzero
#print axioms R1Z.PV_Inv_ScanCost.erases
#print axioms R1Z.PV_Inv_ScanCost.length
#print axioms R1Z.PV_Inv_ScanCost.safe_values
#print axioms R1Z.PV_Inv_ScanPack.guard_to_operands
#print axioms R1Z.PV_Inv_ScanPack.guard_excludes_none
#print axioms R1Z.PV_Inv_SourceBranch.branch_false
#print axioms R1Z.PV_Inv_SourceTests.all_false
#print axioms R1Z.PV_Inv_UniqueSlot.selected_eq
#print axioms R1Z.PV_Inv_ZeroTraceLimit.same_nonzero_verdict_different_prefix
