import R1Z.PV_Src_DynamicCallEquation

/-! Field-by-field transcription of the source mapper after its path-array
loop. The actual extracted direction closure is executed. This is a new
explicit body, not an installation of the opaque Records.call dictionary.
The source-to-dictionary association remains a separate obligation. -/
set_option autoImplicit false
namespace R1Z.PV_Src_MapperBody
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

abbrev Input := pair_forest_trace.PoolV1PairForestInputNoteWitnessV1
abbrev Note := payment_relation.PoolV1OutputNoteWitnessV1
abbrev Snapshot := pair_tree_profile.PoolV1PairLiveSnapshotV1

def witness (i : Input) (out : U32) (rec : Option Note) (chg : Note)
    (bits : Array U32 24#usize) : pair_forest_copy_builder.RW where
  input_value := i.pair.value
  output_value := out
  change_value := chg.value
  sk := i.pair.nullifier_key
  salt := i.pair.salt
  bits := bits
  sibs := BuilderRecordsPath.siblings (PV_Src_NativeDirections.reference i)
  pair_first := i.pair.pair_leaf.first_commitment
  pair_occupied := i.pair.pair_leaf.second_occupied
  pair_second := i.pair.pair_leaf.second_commitment
  pair_inverse := i.pair.pair_leaf.second_occupancy_inverse
  recipient_owner := match rec with | some n => n.owner_key | none => Array.repeat 8#usize 0#u32
  recipient_salt := match rec with | some n => n.salt | none => Array.repeat 8#usize 0#u32
  change_owner := chg.owner_key
  change_salt := chg.salt

def publicRecord (rec : Option Note) (s : Snapshot) (asset : U32)
    (roots : BuilderRecordsReference.Roots) : pair_forest_copy_builder.RP where
  transfer := rec.isSome
  asset := asset
  next_pair_index := s.next_pair_index
  frontier := s.frontier
  empty := BuilderRecordsPublic.empty20 roots

def call [ExternalLinear] (i : Input) (out : U32) (rec : Option Note)
    (chg : Note) (s : Snapshot) (asset : U32) := do
  let bits ← PV_Src_NativeDirections.run i
  let roots ← pair_trace.pair_empty_roots
  ok (witness i out rec chg bits, publicRecord rec s asset roots)

theorem witness_eq (i : Input) (out : U32) (rec : Option Note) (chg : Note) :
    witness i out rec chg (BuilderRecordsPath.bits (PV_Src_NativeDirections.reference i)) =
      PV_Src_RecordReference.witness
        (BuilderRecordsReference.witness (PV_Src_NativeDirections.reference i)
          out (rec.map PV_Src_RecordReference.note) (PV_Src_RecordReference.note chg)) := by
  cases rec with
  | none =>
    simp only [witness,PV_Src_RecordReference.witness,BuilderRecordsReference.witness,
      Option.map_none,BuilderRecordsRecipient.owner,BuilderRecordsRecipient.salt,
      PV_Src_NativeDirections.reference,PV_Src_RecordReference.note,
      AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.ZERO8]
  | some n => rfl

theorem public_eq (rec : Option Note) (s : Snapshot) (asset : U32)
    (roots : BuilderRecordsReference.Roots) :
    publicRecord rec s asset roots = PV_Src_RecordReference.publicRecord
      (BuilderRecordsReference.publicRecord (rec.map PV_Src_RecordReference.note)
        (PV_Src_RecordReference.snapshot s) asset roots) := by
  cases rec <;> rfl

/-- No success assumption, bounded input, hash stub or range premise. This
compares the new explicit body with the owned reference, not actualRecords. -/
theorem call_eq [ExternalLinear] (i : Input) (out : U32) (rec : Option Note)
    (chg : Note) (s : Snapshot) (asset : U32) :
    call i out rec chg s asset = PV_Src_RecordDynamic.call i out rec chg s asset := by
  rw [call,PV_Src_NativeDirections.run_eq]
  simp only [bind_tc_ok]
  change (do let roots ← pair_trace.pair_empty_roots
             ok (witness i out rec chg (BuilderRecordsPath.bits (PV_Src_NativeDirections.reference i)),
               publicRecord rec s asset roots)) =
    @Records.call PV_Src_RecordDynamic.dictionary i out rec chg s asset
  rw [PV_Src_DynamicCallEquation.call]
  simp only [PV_Src_DynamicCallEquation.returned,witness_eq,public_eq]

#print axioms witness_eq
#print axioms public_eq
#print axioms call_eq
end R1Z.PV_Src_MapperBody
