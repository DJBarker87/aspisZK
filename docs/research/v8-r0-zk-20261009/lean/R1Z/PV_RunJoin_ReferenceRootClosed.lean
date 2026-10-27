import R1Z.PV_RunJoin_RecordsReference
import R1Z.PV_RunJoin_ShippedExternal
import R1Z.PV_Src_RecordRootClosed

/-! Consume the published srcid root closure read-only. These remain reference
identifications: no installed Records or shipped source mapper is inferred. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ReferenceRootClosed
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_RunJoin_ShippedExternal

theorem roots : @pair_trace.pair_empty_roots E_shipped =
    ok PV_Src_CanonicalRoots.table := PV_Src_RootHelper.source

theorem call (w : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    @Records.call (PV_RunJoin_RecordsReference.dictionary E_shipped) w out rec change snapshot asset =
      PV_Src_RecordReference.call PV_Src_CanonicalRoots.table w out rec change snapshot asset := by
  rw [PV_RunJoin_RecordsReference.call_eq_dynamic]
  exact PV_Src_RecordRootClosed.call w out rec change snapshot asset

#print axioms roots
#print axioms call
end R1Z.PV_RunJoin_ReferenceRootClosed
