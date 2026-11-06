import NDI_BatchRef.Funs
set_option autoImplicit false
namespace NDI_BatchControl
open Aeneas Aeneas.Std Result

theorem initial : NDI_BatchRef.batch_init_ref=ok (Array.repeat 16#usize 0#u64) := rfl

theorem active (start finish : Usize) (room : start.val<finish.val) (cap : finish.val≤16) :
    ∃ next, next.val=start.val+1 ∧
      NDI_BatchRef.range_ref start finish=ok (true,start,next,finish) := by
  obtain ⟨next,inc,nextVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=start) (y:=1#usize) (by scalar_tac))
  refine ⟨next,nextVal,?_⟩
  have h : start<finish := room
  simp only [NDI_BatchRef.range_ref,if_pos h,inc,bind_tc_ok]

theorem done (finish : Usize) :
    NDI_BatchRef.range_ref finish finish=ok (false,0#usize,finish,finish) := by
  simp only [NDI_BatchRef.range_ref,lt_self_iff_false,if_false]

theorem reached (lo n tree : Nat) (split : (lo=0 ∧ n=10) ∨ (lo=10 ∧ n=12))
    (kind : tree<3) (j : Nat) (more : j<n) :
    lo≤22 ∧ n≤16 ∧ lo+n≤22 ∧ j<n ∧ tree<3 ∧ lo+j<22 ∧ j<16 := by
  rcases split with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega

#print axioms initial
#print axioms active
#print axioms done
#print axioms reached
end NDI_BatchControl
