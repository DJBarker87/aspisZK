import R1Z.PV_RunJoin_ConsumerBoundary25
import PV_L2C_VecShape
import PV_L2C_PackedMasks
import PV_L2C_ExtractedM31Fold
import PV_L2C_ExtractedRows
import PV_L2C_VecWrite
import PV_L2C_PaddingProducer
import PV_L2C_PaddingConsumer
import PV_L2C_M31
import PV_L2C_NativeFold
import PV_L2C_NativeBalance
import PV_L2C_NativeQ
import PV_L2C_QBalance
import PV_L2C_Reducer
import PV_L2C_SampleCanonical
import PV_L2C_CanonicalParser
import PV_L2C_QFold
import PV_L2C_PaddingNative
import PV_L2C_SparseFold
import PV_L2C_ReferenceArithmetic
import PV_L2C_SubPrimitive
import PV_L2C_NormalizeSource
import PV_L2C_ReferenceSub
import PV_L2C_ReferenceQ
import PV_L2C_FirstInactive
import PV_L2C_VecRead
import PV_L2C_ExtractedFold

/-! Combined local-laws audit. No native HonestInput guard refinement is asserted. -/
#print axioms PV_L2C_PaddingProducer.sampled_active
#print axioms PV_L2C_PaddingProducer.balanced_active
#print axioms PV_L2C_PaddingProducer.balanced_sum
#print axioms PV_L2C_PaddingProducer.padding_guards
#print axioms PV_L2C_PaddingConsumer.active_branch
#print axioms PV_L2C_PaddingConsumer.sum_branch
#print axioms PV_L2C_PaddingConsumer.scan_false
#print axioms PV_L2C_PaddingConsumer.all_active_branches
#print axioms PV_L2C_M31.subtractP_branch
#print axioms PV_L2C_M31.subtractP_nat
#print axioms PV_L2C_M31.subtractP_canonical
#print axioms PV_L2C_M31.add_nat
#print axioms PV_L2C_M31.add_canonical
#print axioms PV_L2C_M31.add_decode
#print axioms PV_L2C_M31.subtractP_decode
#print axioms PV_L2C_M31.sub_input_nat
#print axioms PV_L2C_M31.sub_canonical
#print axioms PV_L2C_M31.sub_decode
#print axioms PV_L2C_M31.decode_injective
#print axioms PV_L2C_M31.zero_guard
#print axioms PV_L2C_NativeFold.fold_canonical
#print axioms PV_L2C_NativeFold.fold_decode
#print axioms PV_L2C_NativeFold.fold_zero_decode
#print axioms PV_L2C_NativeFold.negate_decode
#print axioms PV_L2C_NativeBalance.rebalance_canonical
#print axioms PV_L2C_NativeBalance.rebalance_decode_sum
#print axioms PV_L2C_NativeBalance.audit_zero
#print axioms PV_L2C_NativeBalance.audit_branch
#print axioms PV_L2C_NativeQ.zero_canonical
#print axioms PV_L2C_NativeQ.add_canonical
#print axioms PV_L2C_NativeQ.sub_canonical
#print axioms PV_L2C_NativeQ.add_decode
#print axioms PV_L2C_NativeQ.sub_decode
#print axioms PV_L2C_NativeQ.decode_injective
#print axioms PV_L2C_NativeQ.zero_decode
#print axioms PV_L2C_NativeQ.zero_guard
#print axioms PV_L2C_QBalance.fold_component
#print axioms PV_L2C_QBalance.rebalance_component
#print axioms PV_L2C_QBalance.rebalance_audit
#print axioms PV_L2C_QBalance.rebalance_branch
#print axioms PV_L2C_Reducer.first_bound
#print axioms PV_L2C_Reducer.second_bound
#print axioms PV_L2C_Reducer.fold_decode
#print axioms PV_L2C_Reducer.reduction_bound
#print axioms PV_L2C_SampleCanonical.scalar_canonical
#print axioms PV_L2C_SampleCanonical.tuple_canonical
#print axioms PV_L2C_SampleCanonical.secure_canonical
#print axioms PV_L2C_CanonicalParser.word_roundtrip
#print axioms PV_L2C_CanonicalParser.scalar_parse
#print axioms PV_L2C_QFold.canonical_fold
#print axioms PV_L2C_QFold.decode_fold
#print axioms PV_L2C_QFold.tableSum_canonical
#print axioms PV_L2C_QFold.tableSum_decode
#print axioms PV_L2C_QFold.inactive_canonical
#print axioms PV_L2C_QFold.inactive_decode
#print axioms PV_L2C_QFold.native_add_zero
#print axioms PV_L2C_PaddingNative.without_canonical
#print axioms PV_L2C_PaddingNative.excluded_canonical
#print axioms PV_L2C_PaddingNative.rebalance_canonical
#print axioms PV_L2C_PaddingNative.excluded_decode
#print axioms PV_L2C_PaddingNative.rebalance_decode
#print axioms PV_L2C_PaddingNative.raw_sum_zero
#print axioms PV_L2C_PaddingNative.sample_canonical
#print axioms PV_L2C_PaddingNative.active_zero
#print axioms PV_L2C_PaddingNative.guard_outcomes
#print axioms PV_L2C_SparseFold.dense_projection
#print axioms PV_L2C_SparseFold.source_sum
#print axioms PV_L2C_ReferenceArithmetic.m31_add
#print axioms PV_L2C_SubPrimitive.wrapped_sub
#print axioms PV_L2C_SubPrimitive.wrapped_add
#print axioms PV_L2C_NormalizeSource.wrap_eta
#print axioms PV_L2C_NormalizeSource.modulus
#print axioms PV_L2C_NormalizeSource.normalize_native
#print axioms PV_L2C_NormalizeSource.sub_input
#print axioms PV_L2C_NormalizeSource.sub_cut
#print axioms PV_L2C_ReferenceSub.m31_sub
#print axioms PV_L2C_ReferenceQ.source_roundtrip
#print axioms PV_L2C_ReferenceQ.model_roundtrip
#print axioms PV_L2C_ReferenceQ.source_zero
#print axioms PV_L2C_ReferenceQ.add_source
#print axioms PV_L2C_ReferenceQ.sub_source
#print axioms PV_L2C_ReferenceQ.add_actual
#print axioms PV_L2C_ReferenceQ.sub_actual
#print axioms PV_L2C_FirstInactive.returned
#print axioms PV_L2C_FirstInactive.table_returned
#print axioms PV_L2C_VecRead.bound1024
#print axioms PV_L2C_VecRead.read
#print axioms PV_L2C_VecRead.read_active
#print axioms PV_L2C_ExtractedFold.source
#print axioms PV_L2C_ExtractedFold.canonical_sum
#print axioms PV_L2C_ExtractedFold.zero_sum
#print axioms PV_L2C_VecWrite.index_mut
#print axioms PV_L2C_VecWrite.write
#print axioms PV_L2C_ExtractedRows.row_source
#print axioms PV_L2C_ExtractedRows.read_step
#print axioms PV_L2C_ExtractedRows.fold_source
#print axioms PV_L2C_ExtractedM31Fold.source
#print axioms PV_L2C_ExtractedM31Fold.zero_sum
#print axioms PV_L2C_PackedMasks.inserted_bit
#print axioms PV_L2C_PackedMasks.put_contains
#print axioms PV_L2C_PackedMasks.packed_contains
#print axioms PV_L2C_VecShape.length
#print axioms PV_L2C_VecShape.active_read

/-! Exact-carrier non-vacuity audit, merged after admission refusal 42697. -/
set_option autoImplicit false
noncomputable section
namespace PV_L2C_FixtureAudit
open R1Z
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Non-vacuity of exactly the requested carrier, with no guard-success field. -/
theorem transfer : PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K)
    PV_RunJoin_AdmittedCarrier23.transfer :=
  PV_RunJoin_ConsumerBoundary25.transfer_honest
#print axioms transfer

theorem withdrawal : PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K)
    PV_RunJoin_AdmittedCarrier23.withdrawal :=
  PV_RunJoin_ConsumerBoundary25.withdrawal_honest
#print axioms withdrawal

theorem nonempty : ∃ i, PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K) i :=
  ⟨_, transfer⟩
#print axioms nonempty
local instance : CharP PrivacyR1AcctBasis.K 2147483647 :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod AspisCircleGroupOrder.P) PrivacyR1AcctBasis.K).injective AspisCircleGroupOrder.P

/-- Both fixtures at the deployed proof family's concrete field. -/
theorem concrete :
    PV_RunJoin_ConsumerBoundary25.HonestInput (K:=PrivacyR1AcctBasis.K)
      PV_RunJoin_AdmittedCarrier23.transfer ∧
    PV_RunJoin_ConsumerBoundary25.HonestInput (K:=PrivacyR1AcctBasis.K)
      PV_RunJoin_AdmittedCarrier23.withdrawal := ⟨transfer,withdrawal⟩
#print axioms concrete
end PV_L2C_FixtureAudit
