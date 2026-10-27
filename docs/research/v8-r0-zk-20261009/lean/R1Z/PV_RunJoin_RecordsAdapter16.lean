import R1Z.PV_RunJoin_RecordsFuns16
import R1Z.PV_RunJoin_ShippedExternal
import R1Z.PV_Src_RecordDynamic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RecordsAdapter16
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
def input (i : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) : PV_RunJoin_Records.pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1 where
  pair := {
    nullifier_key := i.pair.nullifier_key
    salt := i.pair.salt
    value := i.pair.value
    pair_leaf := {
      first_commitment := i.pair.pair_leaf.first_commitment
      second_occupied := i.pair.pair_leaf.second_occupied
      second_commitment := i.pair.pair_leaf.second_commitment
      second_occupancy_inverse := i.pair.pair_leaf.second_occupancy_inverse }
    selected_second := i.pair.selected_second
    membership := {siblings := i.pair.membership.siblings,index := i.pair.membership.index} }
  super_root_siblings := i.super_root_siblings
  super_root_directions := i.super_root_directions

def note (n : payment_relation.PoolV1OutputNoteWitnessV1) : PV_RunJoin_Records.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1 where
  owner_key := n.owner_key
  salt := n.salt
  value := n.value

def snapshot (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) : PV_RunJoin_Records.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool := s.pool
  deployment_domain := s.deployment_domain
  sequence := s.sequence
  next_pair_index := s.next_pair_index
  current_root := s.current_root
  frontier := s.frontier

def witness (w : PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.RW) : pair_forest_copy_builder.RW where
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

def publicRecord (p : PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.RP) : pair_forest_copy_builder.RP where
  transfer := p.transfer
  asset := p.asset
  next_pair_index := p.next_pair_index
  frontier := p.frontier
  empty := p.empty

def R_shipped (empty : Array (Array U32 8#usize) 21#usize) : Records :=
  ⟨fun i out rec chg snap asset => do
    let (w,p) ← PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.records
      (input i) out (rec.map note) (note chg) (snapshot snap) asset empty
    ok (witness w, publicRecord p)⟩

theorem raw_owned_all_words (d : Array U32 8#usize) :
    PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.records.raw_owned d = ok d :=
  BuilderRecordsReference.raw_owned d

#print axioms input
#print axioms note
#print axioms snapshot
#print axioms witness
#print axioms publicRecord
#print axioms R_shipped
#print axioms raw_owned_all_words
end R1Z.PV_RunJoin_RecordsAdapter16
