import XRv_QueryDriverTotal
open Aeneas Aeneas.Std Result
open XRn_Join_Release
set_option autoImplicit false
namespace XRv_SelectedAdvance
open XRv_QueryDriver XRv_QueryDriverTotal

theorem step_selected (blocks advances : Array (Array U8 32#usize) 8#usize)
 (s out : State) (i : Nat) (hi : i<8) (run : step blocks advances s i = ok out) :
 out.2.2.2 = s.2.2.2 ∨ Array.index_usize advances (XRn_Join_usize i) = ok out.2.2.2 := by
 rcases s with ⟨a,d,stop,state⟩
 cases stop with
 | true =>
   have he : (a,d,true,state)=out := Result.ok.inj run
   subst out
   exact Or.inl rfl
 | false =>
   have hb := index blocks i hi
   have ha := index advances i hi
   unfold step at run
   simp only [Bool.false_eq_true,↓reduceIte,hb,ha,bind_tc_ok] at run
   generalize hw : (XRt_QueryWords.words (blocks.val[i]'(by have h : blocks.val.length=8 := blocks.property; omega))).foldl
     XRn_Join_scanWord (a,d,false) = triple at run
   rcases triple with ⟨as',ds',stop'⟩
   have he := Result.ok.inj run
   subst out
   exact Or.inr ha

theorem fold_selected (blocks advances : Array (Array U8 32#usize) 8#usize)
 (indices : List Nat) (bounded : ∀ i ∈ indices, i<8) (s out : State)
 (run : indices.foldlM (step blocks advances) s = ok out) :
 out.2.2.2 = s.2.2.2 ∨
 ∃ i ∈ indices, Array.index_usize advances (XRn_Join_usize i) = ok out.2.2.2 := by
 induction indices generalizing s with
 | nil =>
   have he : s=out := Result.ok.inj run
   exact Or.inl (congrArg (fun q : State => q.2.2.2) he.symm)
 | cons i rest ih =>
   obtain ⟨next,hn⟩ := step_total blocks advances s i (bounded i (by simp))
   have hr : rest.foldlM (step blocks advances) next = ok out := by
     simpa only [List.foldlM_cons,hn,bind_tc_ok] using run
   rcases ih (fun j hj => bounded j (List.mem_cons_of_mem i hj)) next hr with hsame | ⟨j,hj,hsel⟩
   · rcases step_selected blocks advances s next i (bounded i (by simp)) hn with hprev | hsel
     · exact Or.inl (hsame.trans hprev)
     · exact Or.inr ⟨i,by simp,hsame ▸ hsel⟩
   · exact Or.inr ⟨j,List.mem_cons_of_mem i hj,hsel⟩

#print axioms step_selected
#print axioms fold_selected
end XRv_SelectedAdvance
