import NDO_JGa_Map
import RPv_FJh_InternalPairValue
import NIH_InternalRound
import NFT_DotSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_InternalMaps
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM cell P)
open FIw_ArrayValue (canonical)
open FJh_InternalWeights (index rows callback)
/-- Seven positions of the SAME native map, with no selector reselection. -/
theorem row_member (x : Usize) (hx : x∈rows.val) : ∃ i : Fin 7,index i=x := by
 obtain ⟨j,hj,eq⟩ := List.getElem_of_mem hx
 refine ⟨⟨j,by simpa [rows.property] using hj⟩,?_⟩
 exact eq

theorem weights (l : State) (hl : canonical l) :
 ∃ w,FIq_Native.core.array.Array.map callback rows l=ok w ∧ canonical w := by
 obtain ⟨w,run,cw⟩ := JGa_Map.source callback FIv_NativeValue.Canon rows l (by
   intro x hx
   obtain ⟨i,rfl⟩ := row_member x hx
   have hi : (index i).val<(16#usize).val := by
     rw [FJh_InternalWeights.index_value];have := i.isLt;change i.val+2<16;omega
   let q := cell l ⟨(index i).val,hi⟩
   have rq : Array.index_usize l (index i)=ok q :=
     RawPoseidonExternalRowReads.array_index_usize_ok l (index i) hi
   refine ⟨q,?_,hl _ (List.getElem_mem _)⟩
   change (do let v ← Array.index_usize l (index i);ok (v,l))=ok (q,l)
   rw [rq,bind_tc_ok])
 exact ⟨w,run,cw⟩

theorem constants_even : ∃ e,FIq_Native.core.array.Array.map FJh_InternalConstantCalls.even rows ()=ok e ∧
 (∀ x∈e.val,x.val<P) := by
 obtain ⟨e,run,ce⟩ := JGa_Map.source FJh_InternalConstantCalls.even (fun x : U32=>x.val<P) rows () (by
   intro x hx
   obtain ⟨i,rfl⟩ := row_member x hx
   exact ⟨_,FJh_InternalConstantCalls.even_call i,FJh_InternalConstants.canonical _⟩)
 exact ⟨e,run,ce⟩

theorem constants_odd : ∃ o,FIq_Native.core.array.Array.map FJh_InternalConstantCalls.odd rows ()=ok o ∧
 (∀ x∈o.val,x.val<P) := by
 obtain ⟨o,run,co⟩ := JGa_Map.source FJh_InternalConstantCalls.odd (fun x : U32=>x.val<P) rows () (by
   intro x hx
   obtain ⟨i,rfl⟩ := row_member x hx
   exact ⟨_,FJh_InternalConstantCalls.odd_call i,FJh_InternalConstants.canonical _⟩)
 exact ⟨o,run,co⟩
#print row_member
#print axioms row_member
#print weights
#print axioms weights
#print constants_even
#print axioms constants_even
#print constants_odd
#print axioms constants_odd
end AspisR1.NKG_InternalMaps
end
