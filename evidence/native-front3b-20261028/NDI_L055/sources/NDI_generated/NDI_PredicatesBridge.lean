import NDI_PredicatesRef.Funs
set_option autoImplicit false
namespace NDI_PredicatesBridge
open Aeneas Aeneas.Std Result

theorem tail (x : U8) : NDI_PredicatesRef.tail_predicate_ref x=ok (decide (x≠0#u8)) := by
  simp [NDI_PredicatesRef.tail_predicate_ref]

theorem contains (x q : U32) : NDI_PredicatesRef.contains_predicate_ref x q=ok (decide (q=x)) := by
  simp [NDI_PredicatesRef.contains_predicate_ref,eq_comm]

theorem window (offset count : Usize) (fit : offset.val+count.val≤1768) :
    ∃ finish, finish.val=offset.val+count.val ∧
      NDI_PredicatesRef.window_meta_ref offset count=ok (true,count,finish) := by
  obtain ⟨finish,add,value⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=offset) (y:=count) (by scalar_tac))
  exact ⟨finish,value,by simp only [NDI_PredicatesRef.window_meta_ref,add,bind_tc_ok]⟩

theorem iterator_active (count : Usize) (active : 0<count.val) :
    ∃ rest, rest.val=count.val-1 ∧
      NDI_PredicatesRef.iter_meta_ref count=ok (true,true,rest) := by
  obtain ⟨rest,sub,value⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x:=count) (y:=1#usize) (by scalar_tac))
  have h : count>0#usize := active
  exact ⟨rest,value,by simp only [NDI_PredicatesRef.iter_meta_ref,if_pos h,sub,bind_tc_ok]⟩

theorem iterator_done : NDI_PredicatesRef.iter_meta_ref 0#usize=ok (false,true,0#usize) := rfl

#print axioms tail
#print axioms contains
#print axioms window
#print axioms iterator_active
#print axioms iterator_done
end NDI_PredicatesBridge
