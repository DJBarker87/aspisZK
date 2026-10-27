import R1Z.PV_Src_RecordReference
import R1Z.PV_Src_PublicRecords
import R1Z.BuilderCanonical

/-! Native carrier encodings of canonical witnesses. The membership index is
explicit representation data: Checked does not constrain path direction/index
association, which is retained for the full canonical source join. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CheckedEncoding
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort.pool_v1
abbrev W := AspisR1.SpendRelation.Wspend

def arr3 {α : Type} (f : Fin 3 → α) : Array α 3#usize := ⟨List.ofFn f,by simp⟩

theorem arr3_get {α : Type} [Inhabited α] (f : Fin 3 → α) (l : Nat) (hl : l < 3) :
    (arr3 f).val[l]! = f ⟨l,hl⟩ := by
  show (List.ofFn f)[l]! = _
  rw [List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hl]
  rfl

def nativeWitness (w : W) (index : U32) : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1 where
  pair := {
    nullifier_key := d32 w.sk
    salt := d32 w.salt
    value := v32 w.inputValue
    pair_leaf := {
      first_commitment := d32 w.pair.firstCommitment
      second_occupied := w32 w.pair.secondOccupied
      second_commitment := d32 w.pair.secondCommitment
      second_occupancy_inverse := w32 w.pair.secondOccupancyInverse }
    selected_second := (w.path 0).1
    membership := {
      siblings := arr20 (fun l => d32 (w.path ⟨l.val+1,by omega⟩).2)
      index := index } }
  super_root_siblings := arr3 (fun l => d32 (w.path ⟨l.val+21,by omega⟩).2)
  super_root_directions := arr3 (fun l => (w.path ⟨l.val+21,by omega⟩).1)

def change (w : W) : payment_relation.PoolV1OutputNoteWitnessV1 :=
  ⟨d32 w.changeOwner,d32 w.changeSalt,v32 w.changeValue⟩

def recipient (w : W) : payment_relation.PoolV1OutputNoteWitnessV1 :=
  ⟨d32 w.recipientOwner,d32 w.recipientSalt,v32 w.outputValue⟩

def transferRequest (p : BuilderPublicProjection.Transfer) (w : W) : PV_Src_NativeInput.Request :=
  .transfer p (recipient w)

def withdrawalRequest (p : BuilderPublicProjection.Withdrawal) (w : W) : PV_Src_NativeInput.Request :=
  .withdrawal {p with amount := v32 w.outputValue}

def input (w : W) (request : PV_Src_NativeInput.Request) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) : PV_Src_NativeInput.Input :=
  ⟨request,nativeWitness w index,change w,laneAnchor,snapshot,compiled⟩

theorem checked (w : W) (request : PV_Src_NativeInput.Request) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize)
    (output : PV_Src_NativeInput.outputValue request = v32 w.outputValue) :
    PV_Src_RecordReference.Checked (input w request index snapshot compiled laneAnchor) where
  values := by
    change (v32 w.inputValue).val < 2^30 ∧
      (PV_Src_NativeInput.outputValue request).val < 2^30 ∧ (v32 w.changeValue).val < 2^30
    rw [output,v32_val,v32_val,v32_val]
    exact ⟨w.inputValue.isLt,w.outputValue.isLt,w.changeValue.isLt⟩
  first := d32_canon _
  second := d32_canon _
  membership := by
    intro l hl
    change Canon8 ((arr20 _).val[l]!)
    rw [arr20_get _ l hl]
    exact d32_canon _
  superRoot := by
    intro l hl
    change Canon8 ((arr3 _).val[l]!)
    rw [arr3_get _ l hl]
    exact d32_canon _

#print axioms arr3_get
#print axioms checked
end R1Z.PV_Src_CheckedEncoding
