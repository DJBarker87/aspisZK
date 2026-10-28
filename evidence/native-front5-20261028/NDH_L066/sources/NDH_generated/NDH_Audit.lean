import NDH_Arithmetic
import NDH_ArrayIndex
import NDH_BlockRank
import NDH_CanonicalWide
import NDH_Cast
import NDH_Cmr
import NDH_Decode8
import NDH_FromFnTotal
import NDH_Geometry
import NDH_HashBridge
import NDH_MerkleGrammar
import NDH_NativeDomains
import NDH_PolicySlot
import NDH_Pow5
import NDH_Qm31NativeJoin
import NDH_Qm31Pass
import NDH_Qm31Result
import NDH_QueryFinish
import NDH_Qwrite
import NDH_RegistryActiveSlots
import NDH_RegistryAssociation
import NDH_RegistryBinding
import NDH_RegistryPrimitives
import NDH_RegistrySlots
import NDH_RegistryTail
import NDH_ResultLaws
import NDH_SlotInduction
import NDH_Slots
import NDH_TableInstalled
import NDH_TranscriptBridge

-- Final import and standard-axioms audit; local packets only.
#print axioms NDH_Arithmetic.native_cast
#print axioms NDH_Arithmetic.no_wrap
#print axioms NDH_Arithmetic.lift_identity
#print axioms NDH_Arithmetic.product
#print axioms NDH_Arithmetic.shift_no_wrap
#print axioms NDH_Arithmetic.subtract_no_wrap
#print axioms NDH_Arithmetic.relation
#print axioms NDH_Arithmetic.native_pack
#print axioms NDH_ArrayIndex.array_index_usize_ok
#print axioms NDH_BlockRank.total
#print axioms NDH_CanonicalWide.rem_success
#print axioms NDH_CanonicalWide.reduced_val
#print axioms NDH_CanonicalWide.reduced_eq_self
#print axioms NDH_CanonicalWide.canonical_success
#print axioms NDH_Cast.cohort_cast
#print axioms NDH_Cmr.add
#print axioms NDH_Cmr.sub
#print axioms NDH_Cmr.reference
#print axioms NDH_Decode8.reference
#print axioms NDH_FromFnTotal.from_fn_total
#print axioms NDH_FromFnTotal.loop_total
#print axioms NDH_Geometry.get
#print axioms NDH_Geometry.table
#print axioms NDH_HashBridge.leaf
#print axioms NDH_HashBridge.parent
#print axioms NDH_MerkleGrammar.row_ofFn
#print axioms NDH_MerkleGrammar.chunks
#print axioms NDH_MerkleGrammar.node
#print axioms NDH_NativeDomains.low_digits_decode_domain
#print axioms NDH_PolicySlot.at_call
#print axioms NDH_PolicySlot.preserves_digest
#print axioms NDH_Pow5.fifth_mod
#print axioms NDH_Pow5.value
#print axioms NDH_Qm31NativeJoin.decoded_lists_injective
#print axioms NDH_Qm31NativeJoin.words_injective
#print axioms NDH_Qm31NativeJoin.native_result
#print axioms NDH_Qm31Pass.loop_eq
#print axioms NDH_Qm31Pass.pass_eq
#print axioms NDH_Qm31Result.result
#print axioms NDH_QueryFinish.reference
#print axioms NDH_Qwrite.reference
#print axioms NDH_RegistryActiveSlots.v1_call
#print axioms NDH_RegistryActiveSlots.v2_call
#print axioms NDH_RegistryAssociation.immutable_at_call
#print axioms NDH_RegistryAssociation.paused_at_call
#print axioms NDH_RegistryBinding.reference
#print axioms NDH_RegistryBinding.all_zero
#print axioms NDH_RegistryPrimitives.retirement_v1
#print axioms NDH_RegistryPrimitives.retirement_v2
#print axioms NDH_RegistryPrimitives.pending
#print axioms NDH_RegistryPrimitives.active
#print axioms NDH_RegistryPrimitives.paused
#print axioms NDH_RegistryPrimitives.retired
#print axioms NDH_RegistryPrimitives.invalid
#print axioms NDH_RegistrySlots.immutable_v1
#print axioms NDH_RegistrySlots.paused_v1
#print axioms NDH_RegistrySlots.immutable_v2
#print axioms NDH_RegistrySlots.paused_v2
#print axioms NDH_RegistrySlots.digest_preserved
#print axioms NDH_RegistrySlots.error_preserved
#print axioms NDH_RegistryTail.v1
#print axioms NDH_RegistryTail.v2
#print axioms NDH_ResultLaws.right
#print axioms NDH_ResultLaws.assoc
#print axioms NDH_SlotInduction.invariant
#print axioms NDH_SlotInduction.exists_trace
#print axioms NDH_SlotInduction.completion
#print axioms NDH_Slots.reference
#print axioms NDH_Slots.step
#print axioms NDH_Slots.representable
#print axioms NDH_TableInstalled.reference
#print axioms NDH_TranscriptBridge.new_reference
#print axioms NDH_TranscriptBridge.absorb_reference
