import RPv_FJh_InternalConstantCalls
import NDO_JGa_Map
import RPv_JFy_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_InternalMaps
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM cell)
open FJh_InternalWeights (rows index callback)
open FIw_ArrayValue (canonical)

theorem member (x : Usize) (hx : x ∈ rows.val) : ∃ i : Fin 7, x=index i := by
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem hx
  exact ⟨⟨j,by simpa [rows.property] using hj⟩,he.symm⟩
#print axioms member

theorem weights (l : State) (hl : canonical l) :
    ∃ w : Array QM 7#usize, FIq_Native.core.array.Array.map callback rows l=ok w ∧ canonical w := by
  apply JGa_Map.source callback FIv_NativeValue.Canon rows l
  intro x hx
  obtain ⟨i,rfl⟩ := member x hx
  obtain ⟨q,rq,cq⟩ := JFy_ArrayTotal.read l (index i)
    (by rw [FJh_InternalWeights.index_value]; change i.val+2<16;omega) hl
  exact ⟨q,by simpa [callback,
    state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
    rq,bind_tc_ok],cq⟩
#print axioms weights

theorem constants (parity : Bool) :
    ∃ v : Array U32 7#usize,
      FIq_Native.core.array.Array.map
        (if parity then FJh_InternalConstantCalls.odd else FJh_InternalConstantCalls.even) rows ()=ok v ∧
      ∀ x ∈ v.val, x.val<AspisV8R17.RawReducer.P := by
  apply JGa_Map.source _ (fun x : U32=>x.val<AspisV8R17.RawReducer.P) rows ()
  intro x hx
  obtain ⟨i,rfl⟩ := member x hx
  cases parity
  · exact ⟨_,FJh_InternalConstantCalls.even_call i,FJh_InternalConstants.canonical _⟩
  · exact ⟨_,FJh_InternalConstantCalls.odd_call i,FJh_InternalConstants.canonical _⟩
#print axioms constants
end AspisR1.JGl_InternalMaps
end
