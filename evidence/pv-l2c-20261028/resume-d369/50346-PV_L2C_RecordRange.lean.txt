import PV_L2C_DigestOrigin
import PV_L2C_BlockRange
import R1Z.PV_RunJoin_UniversalRecords22
import R1Z.BuilderRecordCanonical
set_option autoImplicit false
noncomputable section
namespace PV_L2C_RecordRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1Z PV_Src_NativeInput

/-- Raw field facts supplied by successful input validation and the output
origin route. No trace cell or prover guard appears in this interface. -/
structure Fields (i : Input) : Prop where
  key : Canon8 i.witness.pair.nullifier_key
  salt : Canon8 i.witness.pair.salt
  occupied : i.witness.pair.pair_leaf.second_occupied.val < 2147483647
  inverse : i.witness.pair.pair_leaf.second_occupancy_inverse.val < 2147483647
  recipient : ∀ note, recipient i.request = some note →
    PV_L2C_DigestOrigin.Origin note.owner_key ∧ PV_L2C_DigestOrigin.Origin note.salt
  changeOwner : PV_L2C_DigestOrigin.Origin i.change.owner_key
  changeSalt : PV_L2C_DigestOrigin.Origin i.change.salt

theorem optional_owner (rec : Option BuilderRecordsReference.Note)
    (hc : ∀ r, rec = some r → Canon8 r.owner_key) :
    Canon8 (BuilderRecordsRecipient.owner rec) := by
  cases rec with
  | none =>
    intro j hj
    with_unfolding_all exact PV_L2C_BlockRange.zeros 8#usize j (by simpa using hj)
  | some r => exact hc r rfl
#print axioms optional_owner

theorem optional_salt (rec : Option BuilderRecordsReference.Note)
    (hc : ∀ r, rec = some r → Canon8 r.salt) :
    Canon8 (BuilderRecordsRecipient.salt rec) := by
  cases rec with
  | none =>
    intro j hj
    with_unfolding_all exact PV_L2C_BlockRange.zeros 8#usize j (by simpa using hj)
  | some r => exact hc r rfl
#print axioms optional_salt

theorem records (i : Input) (checked : PV_Src_RecordReference.Checked i)
    (hf : Fields i) :
    BuilderRecordCanonical.CanonicalWords
      (PV_Src_Forest_PrimitiveArguments.wordWitness
        (PV_Src_RecordReference.returned PV_Src_CanonicalRoots.table i).w) := by
  have shape := PV_RunJoin_UniversalRecords22.words i checked _
    (PV_RunJoin_UniversalRecords22.newRecords i)
  refine ⟨shape,hf.key,hf.salt,checked.first,hf.occupied,checked.second,hf.inverse,
    ?_,?_,PV_L2C_DigestOrigin.canonical _ hf.changeOwner,
    PV_L2C_DigestOrigin.canonical _ hf.changeSalt⟩
  · apply optional_owner
    intro r he
    cases hrec : recipient i.request with
    | none => simp only [hrec,Option.map_none] at he;cases he
    | some actual =>
      simp only [hrec,Option.map_some] at he
      cases Option.some.inj he
      exact PV_L2C_DigestOrigin.canonical _ (hf.recipient actual hrec).1
  · apply optional_salt
    intro r he
    cases hrec : recipient i.request with
    | none => simp only [hrec,Option.map_none] at he;cases he
    | some actual =>
      simp only [hrec,Option.map_some] at he
      cases Option.some.inj he
      exact PV_L2C_DigestOrigin.canonical _ (hf.recipient actual hrec).2
#print axioms records
end PV_L2C_RecordRange
