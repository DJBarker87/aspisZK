import NDI_BatchWord
import NBE_KeyLoop
set_option autoImplicit false
namespace NDI_BatchStep
open Aeneas Aeneas.Std Result ControlFlow

theorem step (queries : Array U32 22#usize) (lo n tree j : Usize) (keys : Array U64 16#usize)
    (size : n.val≤16) (fit : lo.val+n.val≤22) (active : j.val<n.val) :
    ∃ next value, next.val=j.val+1 ∧
      value.val=256*(if tree=2#usize then queries.val[lo.val+j.val]!.val/4
        else queries.val[lo.val+j.val]!.val)+j.val ∧
      NDI_BatchRef.batch_keys_ref_loop.body queries lo n tree keys j =
        ok (cont (keys.set j value,next)) := by
  obtain ⟨address,add,addressVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=lo) (y:=j) (by scalar_tac))
  obtain ⟨u,read,uval⟩ := WP.spec_imp_exists
    (Array.index_usize_spec queries address (by scalar_tac))
  obtain ⟨value,word,valueVal⟩ := NDI_BatchWord.word u tree j (by omega)
  obtain ⟨changed,write,changedEq⟩ := WP.spec_imp_exists
    (Array.update_spec keys j value (by scalar_tac))
  obtain ⟨next,inc,nextVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=j) (y:=1#usize) (by scalar_tac))
  have room : lo.val+j.val<queries.val.length := by have length : queries.val.length=22 := queries.property;omega
  have ue : u=queries.val[lo.val+j.val]! := by
    simpa only [addressVal,List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem room,Option.getD_some] using uval
  refine ⟨next,value,nextVal,?_,?_⟩
  · simpa only [ue] using valueVal
  · have h : j<n := active
    simp only [NDI_BatchRef.batch_keys_ref_loop.body,if_pos h,add,read,word,write,inc,
      changedEq,bind_tc_ok]

theorem done_step (queries : Array U32 22#usize) (lo n tree j : Usize) (keys : Array U64 16#usize)
    (terminal : n.val≤j.val) :
    NDI_BatchRef.batch_keys_ref_loop.body queries lo n tree keys j=ok (done keys) := by
  have h : ¬j<n := by scalar_tac
  simp only [NDI_BatchRef.batch_keys_ref_loop.body,if_neg h]

theorem frame (keys : Array U64 16#usize) (j : Usize) (value : U64) (k : Nat) (bound : k<16) :
    (keys.set j value).val[k]! =(if k=j.val then value else keys.val[k]!) := by
  have len := keys.property
  simp only [Array.set,List.getElem!_eq_getElem?_getD,List.getElem?_set]
  by_cases hit : k=j.val <;> simp_all

#print axioms step
#print axioms done_step
#print axioms frame
end NDI_BatchStep
