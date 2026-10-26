import R1Z.PV_Src_RecordReference
import R1Z.BuilderRecordsFields

/-! Reference dictionary using the actual extracted empty-root computation.
This is not an assumed constant root table. Shipped mapper association is the
separate unstubbed P6 check; no such equality is postulated in this file. -/
set_option autoImplicit false
namespace R1Z.PV_Src_RecordDynamic
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput

def call [ExternalLinear]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) := do
  let empty ← pair_trace.pair_empty_roots
  PV_Src_RecordReference.call empty input out rec chg s asset

abbrev dictionary [ExternalLinear] : Records := ⟨call⟩

theorem newRecords_factor [ExternalLinear] (i : Input)
    (r : pair_forest_copy_builder.CopyRecords)
    (h : @newRecords dictionary i = ok r) :
    ∃ roots, pair_trace.pair_empty_roots = ok roots ∧
      @newRecords (PV_Src_RecordReference.withRoots roots) i = ok r := by
  change (do
    let (w,p) ← call i.witness (outputValue i.request) (recipient i.request)
      i.change i.snapshot (forestPublic i.request).asset
    ok (pair_forest_copy_builder.CopyRecords.mk w p)) = ok r at h
  obtain ⟨⟨w,p⟩,hp,hr⟩ := BuilderRecordsFields.bind_ok_inv h
  unfold call at hp
  obtain ⟨roots,hroots,hp⟩ := BuilderRecordsFields.bind_ok_inv hp
  refine ⟨roots,hroots,?_⟩
  change (do
    let (w,p) ← PV_Src_RecordReference.call roots i.witness (outputValue i.request)
      (recipient i.request) i.change i.snapshot (forestPublic i.request).asset
    ok (pair_forest_copy_builder.CopyRecords.mk w p)) = ok r
  rw [hp]
  exact hr

theorem words [ExternalLinear] (i : Input) (checked : PV_Src_RecordReference.Checked i)
    (r : pair_forest_copy_builder.CopyRecords)
    (h : @newRecords dictionary i = ok r) :
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) := by
  obtain ⟨roots,_,hr⟩ := newRecords_factor i r h
  exact PV_Src_RecordReference.words roots i checked r hr

#print axioms newRecords_factor
#print axioms words
end R1Z.PV_Src_RecordDynamic
