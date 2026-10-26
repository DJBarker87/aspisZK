import R1Z.PV_Src_NativeDirections
import R1Z.PV_Src_NativeInput
import R1Z.PV_Src_Forest_PrimitiveArguments
import R1Z.BuilderRecordsReference

/-! Nominal installation of the extracted owned record reference. This is
explicitly a P6 candidate dictionary, not the shipped Records implementation.
Its validity theorem records the primitive caller checks that words needs. -/
set_option autoImplicit false
namespace R1Z.PV_Src_RecordReference
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
abbrev RW := AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.RW
abbrev RP := AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.RP

def note (n : payment_relation.PoolV1OutputNoteWitnessV1) : BuilderRecordsReference.Note where
  owner_key := n.owner_key
  salt := n.salt
  value := n.value

def snapshot (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) : BuilderRecordsReference.Snapshot where
  pool := s.pool
  deployment_domain := s.deployment_domain
  sequence := s.sequence
  next_pair_index := s.next_pair_index
  current_root := s.current_root
  frontier := s.frontier

def witness (w : RW) : pair_forest_copy_builder.RW where
  input_value := w.input_value
  output_value := w.output_value
  change_value := w.change_value
  sk := w.sk
  salt := w.salt
  bits := w.bits
  sibs := w.sibs
  pair_first := w.pair_first
  pair_occupied := w.pair_occupied
  pair_second := w.pair_second
  pair_inverse := w.pair_inverse
  recipient_owner := w.recipient_owner
  recipient_salt := w.recipient_salt
  change_owner := w.change_owner
  change_salt := w.change_salt

def publicRecord (p : RP) : pair_forest_copy_builder.RP where
  transfer := p.transfer
  asset := p.asset
  next_pair_index := p.next_pair_index
  frontier := p.frontier
  empty := p.empty

theorem word_witness (w : RW) :
    PV_Src_Forest_PrimitiveArguments.wordWitness (witness w) =
      BuilderExtractedRecords.rawWitness w := rfl

theorem word_public (p : RP) :
    PV_Src_Forest_PrimitiveArguments.wordPublic (publicRecord p) =
      BuilderExtractedRecords.rawPublic p := rfl

def call (empty : BuilderRecordsReference.Roots)
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) := do
  let (w,p) ← AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.records_reference.records_reference_with_roots
    (PV_Src_NativeDirections.reference input) out (rec.map note) (note chg)
    (snapshot s) asset empty
  ok (witness w, publicRecord p)

def withRoots (empty : BuilderRecordsReference.Roots) : Records := ⟨call empty⟩

def returned (empty : BuilderRecordsReference.Roots) (i : PV_Src_NativeInput.Input) :
    pair_forest_copy_builder.CopyRecords :=
  ⟨witness (BuilderRecordsReference.witness (PV_Src_NativeDirections.reference i.witness)
      (PV_Src_NativeInput.outputValue i.request)
      ((PV_Src_NativeInput.recipient i.request).map note) (note i.change)),
    publicRecord (BuilderRecordsReference.publicRecord
      ((PV_Src_NativeInput.recipient i.request).map note) (snapshot i.snapshot)
      (PV_Src_NativeInput.forestPublic i.request).asset empty)⟩

theorem newRecords_eq (empty : BuilderRecordsReference.Roots) (i : PV_Src_NativeInput.Input) :
    @PV_Src_NativeInput.newRecords (withRoots empty) i = ok (returned empty i) := by
  unfold PV_Src_NativeInput.newRecords pair_forest_copy_builder.CopyRecords.new
    pair_forest_copy_builder.records withRoots call
  rw [BuilderRecordsReference.records]
  rfl

/-- Selected-input validity, not callee output correctness. No semantic spend
relation or full trace equality is concealed in this interface. -/
structure Checked (i : PV_Src_NativeInput.Input) : Prop where
  values : i.witness.pair.value.val < 2^30 ∧
    (PV_Src_NativeInput.outputValue i.request).val < 2^30 ∧ i.change.value.val < 2^30
  first : Canon8 i.witness.pair.pair_leaf.first_commitment
  second : Canon8 i.witness.pair.pair_leaf.second_commitment
  membership : ∀ l, l < 20 → Canon8 i.witness.pair.membership.siblings.val[l]!
  superRoot : ∀ l, l < 3 → Canon8 i.witness.super_root_siblings.val[l]!

theorem words (empty : BuilderRecordsReference.Roots) (i : PV_Src_NativeInput.Input)
    (h : Checked i) (r : pair_forest_copy_builder.CopyRecords)
    (hr : @PV_Src_NativeInput.newRecords (withRoots empty) i = ok r) :
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) := by
  rw [newRecords_eq] at hr
  have he := Result.ok.inj hr
  subst r
  rw [returned,word_witness]
  exact BuilderRecordsAdmission.witness_ok
    (PV_Src_NativeDirections.reference i.witness) _ _ (note i.change)
    h.values h.first h.second h.membership h.superRoot

#print axioms word_witness
#print axioms word_public
#print axioms newRecords_eq
#print axioms words
end R1Z.PV_Src_RecordReference
