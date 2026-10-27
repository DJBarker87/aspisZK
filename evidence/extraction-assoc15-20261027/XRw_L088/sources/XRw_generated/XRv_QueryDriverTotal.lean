import XRv_QueryDriver
open Aeneas Aeneas.Std Result
open XRn_Join_Release
set_option autoImplicit false
namespace XRv_QueryDriverTotal
open XRv_QueryDriver

theorem index {T : Type} (a : Array T 8#usize) (i : Nat) (hi : i<8) :
 Array.index_usize a (XRn_Join_usize i) = ok (a.val[i]'(by have h : a.val.length=8 := a.property; omega)) := by
 have hb : i < UScalar.cMax .Usize+1 := by
   have h : 8 ≤ UScalar.cMax .Usize := by scalar_tac
   omega
 have hv : (XRn_Join_usize i).val = i := by change i % (UScalar.cMax .Usize+1) = i; exact Nat.mod_eq_of_lt hb
 have hidx : i < a.val.length := by have h : a.val.length=8 := a.property; omega
 unfold Array.index_usize
 change (match a.val[(XRn_Join_usize i).val]? with
   | none => fail Error.arrayOutOfBounds
   | some x => ok x) = _
 rw [hv,List.getElem?_eq_getElem hidx]

theorem step_total (blocks advances : Array (Array U8 32#usize) 8#usize)
 (s : State) (i : Nat) (hi : i<8) : ∃ out, step blocks advances s i = ok out := by
 rcases s with ⟨a,d,stop,state⟩
 cases stop with
 | true => exact ⟨_,rfl⟩
 | false =>
   unfold step
   simp only [Bool.false_eq_true,↓reduceIte,index blocks i hi,index advances i hi,bind_tc_ok]
   exact ⟨_,rfl⟩

theorem fold_total (blocks advances : Array (Array U8 32#usize) 8#usize)
 (indices : List Nat) (bounded : ∀ i ∈ indices, i<8) (s : State) :
 ∃ out, indices.foldlM (step blocks advances) s = ok out := by
 induction indices generalizing s with
 | nil => exact ⟨s,rfl⟩
 | cons i rest ih =>
   obtain ⟨next,hn⟩ := step_total blocks advances s i (bounded i (by simp))
   obtain ⟨out,ho⟩ := ih (fun j hj => bounded j (List.mem_cons_of_mem i hj)) next
   refine ⟨out,?_⟩
   rw [List.foldlM_cons,hn,bind_tc_ok]
   exact ho

theorem total (blocks advances : Blocks) :
 ∃ out, aspis_core.r0_transcript.queries_from_pairs blocks advances = ok out := by
 obtain ⟨out,ho⟩ := fold_total blocks advances (List.range 8) (fun i hi => List.mem_range.mp hi)
   ([],0,false,advances.val[7]?.getD (Array.repeat 32#usize 0#u8))
 rw [driver,short_circuit,ho,bind_tc_ok]
 unfold finish
 split <;> exact ⟨_,rfl⟩

#print axioms index
#print axioms step_total
#print axioms fold_total
#print axioms total
end XRv_QueryDriverTotal
