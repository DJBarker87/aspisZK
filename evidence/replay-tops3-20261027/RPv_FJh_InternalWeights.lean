import RPv_FJh_MapCells
import RPv_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalWeights
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM cell Canonical Decode)
open FIw_ArrayValue (canonical decoded)
abbrev rows := state_only_poseidon.interpolated_internal_pair.ROWS
abbrev callback := state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
def index (i : Fin 7) : Usize := cell rows i
theorem index_value (i : Fin 7) : (index i).val=i.val+2 := by
  unfold index cell rows state_only_poseidon.interpolated_internal_pair.ROWS
  fin_cases i <;> rfl
/-- Every output of the actual seven-selector map reads the SAME local array. -/
theorem read (l : State) (w : Array QM 7#usize)
    (run : FIq_Native.core.array.Array.map callback rows l=ok w) (i : Fin 7) :
    Array.index_usize l (index i)=ok (cell w i) := by
  unfold FIq_Native.core.array.Array.map at run
  have rel := FJa_MapRelation.value callback
    (fun j q=>Array.index_usize l j=ok q) rows l w (by
      intro j hj q last called
      change (do let x←Array.index_usize l j;ok (x,l))=ok (q,last) at called
      obtain ⟨x,hx,called⟩ := FIv_Map.bind_success _ _ _ called
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj called)
      exact ⟨hx,rfl⟩) run
  exact FJh_MapCells.get rel i.val (by rw [rows.property];exact i.isLt)
    (by rw [w.property];exact i.isLt)
theorem value (l : State) (w : Array QM 7#usize) (hl : canonical l)
    (run : FIq_Native.core.array.Array.map callback rows l=ok w) :
    canonical w ∧ ∀ i : Fin 7,Decode (cell w i)=decoded l ⟨i.val+2,by change i.val+2<16;omega⟩ := by
  have one (i : Fin 7) := read l w run i
  refine ⟨?_,?_⟩
  · intro x hx
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
    exact FIv_NativeArray.canonical l (index ⟨j,by simpa [w.property] using hj⟩) _ hl
      (one ⟨j,by simpa [w.property] using hj⟩)
  · intro i
    have hi : (index i).val<(16#usize).val := by rw [index_value];have h:=i.isLt;change i.val+2<16;omega
    simpa only [index_value] using FIw_ArrayReadValue.read l (index i) hi (cell w i) (one i)
#print axioms index_value
#print axioms read
#print axioms value
end AspisR1.FJh_InternalWeights
end
