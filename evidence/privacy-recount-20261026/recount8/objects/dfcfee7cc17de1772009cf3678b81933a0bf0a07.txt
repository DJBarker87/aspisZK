import R1Z.BuilderRecordsPath
import R1Z.BuilderRecordsRecipient
import R1Z.BuilderRecordsPublic
import R1Z.BuilderExtractedRecords

/-! Total, all-field refinement of the D90 owned reference. The reference is
not the shipped function: its source equality is the separate named P6 route. -/
set_option autoImplicit false
namespace R1Z.BuilderRecordsReference
open Aeneas Aeneas.Std Result AspisBuilderRecordsReference R0Z.WriterRefine
open pool_v1.pair_forest_copy_builder R1Z.BuilderRecordsArray
abbrev Input := BuilderRecordsPath.Input
abbrev Note := BuilderRecordsRecipient.Note
abbrev Snapshot := BuilderRecordsPublic.Snapshot
abbrev Roots := BuilderRecordsPublic.Roots

def witness (input : Input) (out : U32) (rec : Option Note) (chg : Note) : RW where
  input_value := input.pair.value
  output_value := out
  change_value := chg.value
  sk := input.pair.nullifier_key
  salt := input.pair.salt
  bits := BuilderRecordsPath.bits input
  sibs := BuilderRecordsPath.siblings input
  pair_first := input.pair.pair_leaf.first_commitment
  pair_occupied := input.pair.pair_leaf.second_occupied
  pair_second := input.pair.pair_leaf.second_commitment
  pair_inverse := input.pair.pair_leaf.second_occupancy_inverse
  recipient_owner := BuilderRecordsRecipient.owner rec
  recipient_salt := BuilderRecordsRecipient.salt rec
  change_owner := chg.owner_key
  change_salt := chg.salt

def publicRecord (rec : Option Note) (s : Snapshot) (asset : U32) (empty : Roots) : RP where
  transfer := rec.isSome
  asset := asset
  next_pair_index := s.next_pair_index
  frontier := s.frontier
  empty := BuilderRecordsPublic.empty20 empty

theorem raw_owned (d : Array U32 8#usize) : records_reference.raw_owned d = ok d := by
  rw [records_reference.raw_owned]
  rw [index_ok d 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok d 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok d 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok d 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok d 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok d 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok d 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok d 7#usize (by decide)]
  simp only [bind_tc_ok]
  congr 1
  apply BuilderRecordCanonical.array_ext
  intro i hi
  have hi' : i < 8 := by simpa using hi
  interval_cases i <;> rfl

/-- No success premise, range premise, or array/loop equality is assumed.
All 20 fields are computed, for every machine-word input and both variants. -/
theorem records (input : Input) (out : U32) (rec : Option Note) (chg : Note)
    (s : Snapshot) (asset : U32) (empty : Roots) :
    records_reference.records_reference_with_roots input out rec chg s asset empty =
      ok (witness input out rec chg, publicRecord rec s asset empty) := by
  rw [records_reference.records_reference_with_roots, BuilderRecordsPath.from_zero]
  simp only [bind_tc_ok]
  rw [BuilderRecordsRecipient.loop_spec rec ZERO8 ZERO8 0#usize (by simp)
    (fun _ => ⟨rfl, rfl⟩) (by intro j hj; simp at hj) (by intro j hj; simp at hj)]
  simp only [bind_tc_ok]
  rw [BuilderRecordsPublic.from_zero]
  simp only [bind_tc_ok]
  simp only [raw_owned, bind_tc_ok]
  cases rec <;> rfl

/-- The exact returned record types now feed field normalization. Admission
and the actual empty-root helper meaning remain separately named obligations. -/
theorem normalized_trace
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
    (input : Input) (out : U32) (rec : Option Note) (chg : Note)
    (s : Snapshot) (asset : U32) (empty : Roots) (pub : R0P.Public R1J.SpendWitnessMap.F)
    (hw : WitnessOk (BuilderExtractedRecords.rawWitness (witness input out rec chg)))
    (hp : PubCorr (BuilderExtractedRecords.rawPublic (publicRecord rec s asset empty))
      (R1J.SpendWitnessMap.mapPub (K := K) pub)) :
    BuilderRefinement.mergedTrace (K := K)
      (BuilderExtractedRecords.rawWitness (witness input out rec chg))
      (BuilderExtractedRecords.rawPublic (publicRecord rec s asset empty)) =
      BuilderRefinement.mergedTrace
        (BuilderCanonical.rustWitness (BuilderRecordCanonical.witness
          (BuilderExtractedRecords.rawWitness (witness input out rec chg))))
        (BuilderCanonical.rustPublic pub) :=
  BuilderExtractedRecords.reference_trace _ _ _ hw hp

#print axioms raw_owned
#print axioms records
#print axioms normalized_trace
end R1Z.BuilderRecordsReference
