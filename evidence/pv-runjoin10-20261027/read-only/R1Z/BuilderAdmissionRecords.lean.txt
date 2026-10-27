import R1Z.BuilderAdmissionCommon

/-! Join the successful actual common validator to the exact owned-reference
record types. Forest super-root and output bounds remain primitive caller
checks; the semantic spend/append relation is not assumed or inferred here. -/
set_option autoImplicit false
namespace R1Z.BuilderAdmissionRecords
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderRecordsReference

def sourcePair (input : Input) :
    AspisBuilderAdmissionSource.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1 where
  nullifier_key := input.pair.nullifier_key
  salt := input.pair.salt
  value := input.pair.value
  pair_leaf := {
    first_commitment := input.pair.pair_leaf.first_commitment
    second_occupied := input.pair.pair_leaf.second_occupied
    second_commitment := input.pair.pair_leaf.second_commitment
    second_occupancy_inverse := input.pair.pair_leaf.second_occupancy_inverse }
  selected_second := input.pair.selected_second
  membership := {siblings := input.pair.membership.siblings, index := input.pair.membership.index}

/-- The words field of the runtime join is discharged for these exact mapped
inputs once the actual successful common-validation call and the two forest
range/canonicality checks are supplied. No record/trace conclusion is assumed. -/
theorem words_of_common_success
    (input : Input) (out : U32) (rec : Option Note) (chg : Note)
    (pool domain : Array U8 32#usize) (seq : U64) (anchor nullifier : Array U32 8#usize)
    (asset : U32)
    (context : AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (success : AspisBuilderAdmissionSource.pool_v1.pair_trace.validate_common
      pool domain seq anchor nullifier asset (sourcePair input) context = ok (.Ok ()))
    (outputBounds : out.val < 2^30 ∧ chg.value.val < 2^30)
    (superRoot : ∀ l, l < 3 → Canon8 input.super_root_siblings.val[l]!) :
    WitnessOk (BuilderExtractedRecords.rawWitness (witness input out rec chg)) := by
  have h := BuilderAdmissionCommon.common_facts
    pool domain seq anchor nullifier asset (sourcePair input) context success
  exact BuilderRecordsAdmission.witness_ok input out rec chg
    ⟨h.value_bound, outputBounds⟩ h.pair_first h.pair_second h.membership superRoot

#print axioms words_of_common_success
end R1Z.BuilderAdmissionRecords
