import R1Z.PV_Src_CanonicalNormalize
import R1Z.PV_Src_PackedSelection
import R1Z.PV_Src_CanonicalTransferRecord
import R1Z.PV_Src_CanonicalWithdrawalRecord
import R1Z.PV_Src_RecordAdmission

/-! Private reference records recover every normalized canonical witness.
The admission bridge retains the exact public association as an explicit join;
it does not assert that arbitrary supplied compiler payloads are successful. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CanonicalPrivateRecord
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def input (c : BuilderCanonical.Instance (K := K))
    (pool domain destination : PV_Src_PublicRecords.Context)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize) : PV_Src_NativeInput.Input :=
  let n := PV_Src_CanonicalNormalize.normalize c
  PV_Src_CheckedEncoding.input n.val.2
    (PV_Src_CanonicalRequest.request n pool domain destination)
    (PV_Src_PathIndex.index n.val.2) snapshot compiled anchor

theorem witness (c : BuilderCanonical.Instance (K := K))
    (roots : BuilderRecordsReference.Roots)
    (pool domain destination : PV_Src_PublicRecords.Context)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize) :
    PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_Src_RecordReference.returned roots
        (input c pool domain destination snapshot compiled anchor)).w =
      BuilderCanonical.rustWitness (PV_Src_CanonicalNormalize.normalize c).val.2 := by
  unfold input
  cases hv : c.val.1.variant with
  | privateTransfer =>
    exact PV_Src_CanonicalTransferRecord.witness (PV_Src_CanonicalNormalize.normalize c)
      (by rw [PV_Src_CanonicalNormalize.public_eq]; exact hv)
      roots pool domain destination snapshot compiled anchor
  | withdrawal =>
    have hn : (PV_Src_CanonicalNormalize.normalize c).val.1.variant = .withdrawal := by
      rw [PV_Src_CanonicalNormalize.public_eq]; exact hv
    have he : PV_Src_WithdrawalRecipient.erase (PV_Src_CanonicalNormalize.normalize c).val.2 =
        (PV_Src_CanonicalNormalize.normalize c).val.2 := by
      rw [PV_Src_CanonicalNormalize.withdrawal c hv]
      rfl
    simpa only [he] using
      PV_Src_CanonicalWithdrawalRecord.witness (PV_Src_CanonicalNormalize.normalize c)
        hn roots pool domain destination snapshot compiled anchor

theorem admission (c : BuilderCanonical.Instance (K := K))
    (roots : BuilderRecordsReference.Roots)
    (pool domain destination : PV_Src_PublicRecords.Context)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize)
    (records : pair_forest_copy_builder.CopyRecords)
    (hr : @PV_Src_NativeInput.newRecords (PV_Src_RecordReference.withRoots roots)
      (input c pool domain destination snapshot compiled anchor) = ok records)
    (publicEq : mapPub (K := K) (PV_Src_Public.canonicalPublic
      (PV_Src_NativeInput.publicInput (input c pool domain destination snapshot compiled anchor))) =
      mapPub (K := K) c.val.1) :
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic
        (PV_Src_NativeInput.publicInput (input c pool domain destination snapshot compiled anchor))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness records.w))) := by
  rw [PV_Src_RecordReference.newRecords_eq] at hr
  have he := Result.ok.inj hr
  apply PV_Src_RecordAdmission.selected (PV_Src_CanonicalNormalize.normalize c)
    (input c pool domain destination snapshot compiled anchor) records
  · rw [← he]
    exact witness c roots pool domain destination snapshot compiled anchor
  · rw [PV_Src_CanonicalNormalize.public_eq]
    exact publicEq

#print axioms witness
#print axioms admission
end R1Z.PV_Src_CanonicalPrivateRecord

/-! Final focused axiom audit of the restored bridge cone, not all branch modules. -/
#print axioms R1Z.PV_Src_CanonicalDecode.from_model
#print axioms R1Z.PV_Src_CanonicalDecode.map_self
#print axioms R1Z.PV_Src_CanonicalDecode.roundtrip
#print axioms R1Z.PV_Src_CanonicalNormalize.public_eq
#print axioms R1Z.PV_Src_CanonicalNormalize.transfer
#print axioms R1Z.PV_Src_CanonicalNormalize.withdrawal
#print axioms R1Z.PV_Src_CanonicalRequest.amount
#print axioms R1Z.PV_Src_CanonicalRequest.output_value
#print axioms R1Z.PV_Src_CanonicalRequest.word_value
#print axioms R1Z.PV_Src_CanonicalSibling.sibling
#print axioms R1Z.PV_Src_CanonicalTransferRecord.witness
#print axioms R1Z.PV_Src_CanonicalWithdrawalRecord.request
#print axioms R1Z.PV_Src_CanonicalWithdrawalRecord.witness
#print axioms R1Z.PV_Src_CheckedCanonical.checked
#print axioms R1Z.PV_Src_CheckedCanonical.words
#print axioms R1Z.PV_Src_CheckedEncoding.arr3_get
#print axioms R1Z.PV_Src_CheckedEncoding.checked
#print axioms R1Z.PV_Src_CheckedVariants.transfer_checked
#print axioms R1Z.PV_Src_CheckedVariants.withdrawal_checked
#print axioms R1Z.PV_Src_Forest_BankMerge.check
#print axioms R1Z.PV_Src_Forest_BankMerge.check_loop
#print axioms R1Z.PV_Src_Forest_BankMerge.copy
#print axioms R1Z.PV_Src_Forest_BankMerge.copy_loop
#print axioms R1Z.PV_Src_Forest_BankMerge.model_count
#print axioms R1Z.PV_Src_Forest_BankMerge.source_count
#print axioms R1Z.PV_Src_Forest_DigestArguments.block_digest
#print axioms R1Z.PV_Src_Forest_DigestArguments.chunk
#print axioms R1Z.PV_Src_Forest_DigestArguments.chunk_len
#print axioms R1Z.PV_Src_Forest_DigestArguments.digest8_eq
#print axioms R1Z.PV_Src_Forest_DigestArguments.from_fn_nat
#print axioms R1Z.PV_Src_Forest_DigestArguments.node_digest
#print axioms R1Z.PV_Src_Forest_DigestArguments.note_c2
#print axioms R1Z.PV_Src_Forest_DigestArguments.note_c3
#print axioms R1Z.PV_Src_Forest_DigestArguments.ok_ite
#print axioms R1Z.PV_Src_Forest_DigestArguments.owner
#print axioms R1Z.PV_Src_Forest_DigestArguments.owner_success
#print axioms R1Z.PV_Src_Forest_DigestArguments.perm_eq
#print axioms R1Z.PV_Src_Forest_DigestArguments.pre_state
#print axioms R1Z.PV_Src_Forest_DigestArguments.scalar_eq
#print axioms R1Z.PV_Src_Forest_DigestArguments.sponge_digest
#print axioms R1Z.PV_Src_Forest_DigestArguments.sponge_step_eq
#print axioms R1Z.PV_Src_Forest_Inverse.bit_one
#print axioms R1Z.PV_Src_Forest_Inverse.cast_word_value
#print axioms R1Z.PV_Src_Forest_Inverse.field_power_value
#print axioms R1Z.PV_Src_Forest_Inverse.loop
#print axioms R1Z.PV_Src_Forest_Inverse.multiply_mod
#print axioms R1Z.PV_Src_Forest_Inverse.multiply_prime
#print axioms R1Z.PV_Src_Forest_Inverse.shift_one
#print axioms R1Z.PV_Src_Forest_InverseResult.inverse
#print axioms R1Z.PV_Src_Forest_PrimitiveArguments.aux_callee_withdrawal
#print axioms R1Z.PV_Src_Forest_PrimitiveArguments.in_record
#print axioms R1Z.PV_Src_Forest_PrimitiveArguments.input_correspondence
#print axioms R1Z.PV_Src_Forest_PrimitiveArguments.parts_aux_content_withdrawal
#print axioms R1Z.PV_Src_Forest_PrimitiveArguments.parts_aux_withdrawal
#print axioms R1Z.PV_Src_Forest_PrimitiveArguments.zero_digest
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_P
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_TWEAK
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_m31_add
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_node_absorb
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_node_absorb_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_node_pre
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_node_pre_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_sponge_absorb
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_sponge_absorb_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_sponge_init
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_write_block
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_write_block_ends
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_write_block_ends_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_write_block_rounds
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_write_block_rounds_loop0
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.block_write_block_rounds_loop0_loop0
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_EXTERNAL_FINAL
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_EXTERNAL_INITIAL
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_INTERNAL
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_INTERNAL_SHIFTS
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_P
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_absorb_into
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_absorb_into_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_apply_round
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_ext_add
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_ext_add_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_ext_groups
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_ext_groups_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_ext_sums
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_ext_sums_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_external_linear
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_full_round
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_int_part_sum
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_int_part_sum_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_internal_linear
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_internal_linear_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_internal_round
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_leading_pair
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_m31_add
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_m31_mul
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_mat4
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_perm_rounds
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_perm_rounds_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_pow5
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_sbox_full
#print axioms R1Z.PV_Src_Forest_PrimitiveDigests.poseidon_sbox_full_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.m31_sub
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.path_base_local_row
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_aux_block
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_occupancy_row
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_occupancy_row_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_path_block
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_path_block_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_path_level
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_path_level_loop
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_value_block
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_value_block_loop0
#print axioms R1Z.PV_Src_Forest_PrimitiveWriters.write_value_block_loop0_loop0
#print axioms R1Z.PV_Src_LowBits.sum
#print axioms R1Z.PV_Src_NativeDirections.booleans
#print axioms R1Z.PV_Src_NativeDirections.closure_result
#print axioms R1Z.PV_Src_NativeDirections.reference
#print axioms R1Z.PV_Src_NativeDirections.run_eq
#print axioms R1Z.PV_Src_NativeInput.columns
#print axioms R1Z.PV_Src_NativeInput.newRecords
#print axioms R1Z.PV_Src_NativeInput.publicInput
#print axioms R1Z.PV_Src_NativeInput.run
#print axioms R1Z.PV_Src_NativeInput.transition
#print axioms R1Z.PV_Src_OptionShape.canonical
#print axioms R1Z.PV_Src_OptionShape.reflect
#print axioms R1Z.PV_Src_PackedSelection.bits
#print axioms R1Z.PV_Src_PackedSelection.checked
#print axioms R1Z.PV_Src_PackedSelection.index_bound
#print axioms R1Z.PV_Src_PackedSelection.primitive
#print axioms R1Z.PV_Src_PackedSelection.public_preserved
#print axioms R1Z.PV_Src_PathBits.bit_at
#print axioms R1Z.PV_Src_PathBits.bits
#print axioms R1Z.PV_Src_PathBits.bool_word
#print axioms R1Z.PV_Src_PathIndex.bit
#print axioms R1Z.PV_Src_PathIndex.bound
#print axioms R1Z.PV_Src_PathIndex.value
#print axioms R1Z.PV_Src_PathPacking.bit
#print axioms R1Z.PV_Src_PathPacking.bound
#print axioms R1Z.PV_Src_PathPacking.half
#print axioms R1Z.PV_Src_PathSiblings.at_level
#print axioms R1Z.PV_Src_PathSiblings.siblings
#print axioms R1Z.PV_Src_Public.output_eq
#print axioms R1Z.PV_Src_Public.public_eq
#print axioms R1Z.PV_Src_Public.run_success
#print axioms R1Z.PV_Src_Public.transfer_public_eq
#print axioms R1Z.PV_Src_Public.withdrawal_public_eq
#print axioms R1Z.PV_Src_PublicRecords.public_roundtrip
#print axioms R1Z.PV_Src_PublicRecords.self_digest
#print axioms R1Z.PV_Src_PublicRecords.self_scalar
#print axioms R1Z.PV_Src_RecordAdmission.selected
#print axioms R1Z.PV_Src_RecordDynamic.newRecords_factor
#print axioms R1Z.PV_Src_RecordDynamic.words
#print axioms R1Z.PV_Src_RecordReference.newRecords_eq
#print axioms R1Z.PV_Src_RecordReference.word_public
#print axioms R1Z.PV_Src_RecordReference.word_witness
#print axioms R1Z.PV_Src_RecordReference.words
#print axioms R1Z.PV_Src_ReferenceTransfer.witness
#print axioms R1Z.PV_Src_ReferenceWithdrawal.witness
#print axioms R1Z.PV_Src_WithdrawalRecipient.lift_erase
#print axioms R1Z.PV_Src_WithdrawalRecipient.preserves
#print axioms R1Z.PV_Src_ZeroDigest.encoded
