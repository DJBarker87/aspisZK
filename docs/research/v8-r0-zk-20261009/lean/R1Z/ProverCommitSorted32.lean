import R1Z.ProverCommitPublication32
set_option autoImplicit false
namespace R1Z.ProverCommitSorted32
open Aeneas Aeneas.Std Result R1Z.ProverCommitPublication32
open AspisR1IndexInsert32

/-- Exact tail-copy semantics, including the explicit vector-capacity bound. -/
theorem tail_refines (fuel : Nat) (table out : IndexMap) (pos : Usize)
    (hi : pos.val ≤ table.val.length) (hf : table.val.length-pos.val < fuel)
    (room : out.val.length + (table.val.length-pos.val) ≤ Usize.max) :
    ∃ final, sim.owned32.index_tail table pos out = ok final ∧
      final.val = out.val ++ table.val.drop pos.val := by
  induction fuel generalizing pos out with
  | zero => omega
  | succ fuel ih =>
    rw [sim.owned32.index_tail]
    by_cases done : pos = alloc.vec.Vec.len table
    · have hp : pos.val = table.val.length := congrArg UScalar.val done
      simp only [if_pos done,List.drop_eq_nil_of_le (by omega : table.val.length ≤ pos.val),List.append_nil]
      exact ⟨out,rfl,rfl⟩
    · have more : pos.val < table.val.length := by
        have ne : pos.val ≠ table.val.length := by
          intro eq
          apply done
          apply UScalar.eq_of_val_eq
          exact eq
        omega
      obtain ⟨entry,hr,he⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec table pos more)
      have hd : table.val.drop pos.val = entry :: table.val.drop (pos.val+1) := by
        rw [he]
        exact List.drop_eq_getElem_cons more
      obtain ⟨next,hpush,hval⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out entry (by omega))
      have hlen : next.val.length = out.val.length+1 := by simp only [hval,List.length_append,List.length_singleton]
      have step := next_cursor table pos more
      obtain ⟨final,ht,hfval⟩ := ih next (Usize.wrapping_add pos 1#usize)
        (by omega) (by omega) (by omega)
      refine ⟨final,?_,?_⟩
      · simp only [if_neg done,alloc.vec.Vec.index_slice_index,hr,bind_tc_ok,BuiltinClone,hpush,lift,ht]
      · rw [hfval,hval,step,hd]
        simp only [List.append_assoc,List.singleton_append]

def insert (key : Usize) (value : Bytes) : List (Usize × Bytes) →
    List (Usize × Bytes) × Option Bytes
  | [] => ([(key,value)],none)
  | (k,v)::xs =>
    if key<k then ((key,value)::(k,v)::xs,none)
    else if key=k then ((key,value)::xs,some v)
    else let next := insert key value xs
         ((k,v)::next.1,next.2)

/-- Duplicate replacement and the returned old bytes agree with the list
insertion specification for every finite table (not just the Kani bound). -/
theorem insert_refines (fuel : Nat) (table out : IndexMap) (key : Usize)
    (value : Bytes) (pos : Usize)
    (hi : pos.val ≤ table.val.length) (hf : table.val.length-pos.val < fuel)
    (room : out.val.length + (table.val.length-pos.val) + 1 ≤ Usize.max) :
    ∃ final, sim.owned32.index_insert table key value pos out =
      ok (final,(insert key value (table.val.drop pos.val)).2) ∧
      final.val = out.val ++ (insert key value (table.val.drop pos.val)).1 := by
  induction fuel generalizing pos out with
  | zero => omega
  | succ fuel ih =>
    rw [sim.owned32.index_insert]
    by_cases done : pos = alloc.vec.Vec.len table
    · have hp : pos.val = table.val.length := congrArg UScalar.val done
      obtain ⟨next,hpush,hval⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out (key,value) (by omega))
      simp only [if_pos done,List.drop_eq_nil_of_le (by omega : table.val.length ≤ pos.val),insert,hpush,bind_tc_ok]
      exact ⟨next,rfl,hval⟩
    · have more : pos.val < table.val.length := by
        have ne : pos.val ≠ table.val.length := by
          intro eq
          apply done
          apply UScalar.eq_of_val_eq
          exact eq
        omega
      obtain ⟨entry,hr,he⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec table pos more)
      have hd : table.val.drop pos.val = entry :: table.val.drop (pos.val+1) := by
        rw [he]
        exact List.drop_eq_getElem_cons more
      have step := next_cursor table pos more
      rcases entry with ⟨k,v⟩
      simp only [if_neg done,alloc.vec.Vec.index_slice_index,hr,bind_tc_ok,BuiltinClone]
      by_cases lt : key<k
      · obtain ⟨next,hpush,hval⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out (key,value) (by omega))
        have hn : next.val.length = out.val.length+1 := by simp only [hval,List.length_append,List.length_singleton]
        obtain ⟨final,ht,hfinal⟩ := tail_refines (fuel+1) table next pos hi hf (by omega)
        refine ⟨final,?_,?_⟩
        · simp only [lt,if_true,hpush,bind_tc_ok,ht,hd,insert]
        · rw [hfinal,hval,hd]
          simp only [insert,lt,if_true,List.append_assoc,List.singleton_append]
      · by_cases eq : key=k
        · obtain ⟨next,hpush,hval⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec out (key,value) (by omega))
          have hn : next.val.length = out.val.length+1 := by simp only [hval,List.length_append,List.length_singleton]
          obtain ⟨final,ht,hfinal⟩ := tail_refines fuel table next (Usize.wrapping_add pos 1#usize)
            (by omega) (by omega) (by omega)
          refine ⟨final,?_,?_⟩
          · simp only [if_neg lt,if_pos eq,hpush,bind_tc_ok,lift,ht,hd,insert]
          · rw [hfinal,hval,step,hd]
            simp only [insert,if_neg lt,if_pos eq,List.append_assoc,List.singleton_append]
        · obtain ⟨next,hpush,hval⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec out (k,v) (by omega))
          have hn : next.val.length = out.val.length+1 := by simp only [hval,List.length_append,List.length_singleton]
          obtain ⟨final,ht,hfinal⟩ := ih next (Usize.wrapping_add pos 1#usize)
            (by omega) (by omega) (by omega)
          rw [step] at ht hfinal
          refine ⟨final,?_,?_⟩
          · simp only [lt,eq,if_false,hpush,bind_tc_ok,lift,ht,hd,insert]
          · rw [hfinal,hval,hd]
            simp only [insert,lt,eq,if_false,List.append_assoc,List.singleton_append]

#print axioms insert_refines
#print axioms tail_refines
end R1Z.ProverCommitSorted32
