import TerminalArrayFromFnModelV4Clean
set_option autoImplicit false
namespace AspisR1.NBA_FromFnTotal
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

theorem loop_total {T F : Type} (N : Usize) (cb : core.ops.function.FnMut F Usize T)
    (total : ∀ (f : F) (i : Usize), i.val<N.val → ∃ value next,cb.call_mut f i=ok (value,next))
    (fuel : Nat) (i : Usize) (f : F) (acc : List T)
    (bound : i.val≤N.val) (budget : N.val-i.val≤fuel) :
    ∃ out last,arrayFromFnLoop N cb fuel i f acc=ok (out,last) := by
  induction fuel generalizing i f acc with
  | zero =>
    have done : ¬i<N := by scalar_tac
    exact ⟨acc.reverse,f,by simp only [arrayFromFnLoop,done,↓reduceDIte]⟩
  | succ fuel ih =>
    by_cases active : i<N
    · have hi : i.val<N.val := by scalar_tac
      obtain ⟨value,next,call⟩ := total f i hi
      have small : i.val+(1#usize).val≤UScalar.max .Usize := by scalar_tac
      obtain ⟨j,add,step⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) small)
      have stepval : j.val=i.val+1 := by simpa only [show (1#usize).val=1 by rfl] using step
      obtain ⟨out,last,run⟩ := ih j next (value::acc) (by omega) (by omega)
      refine ⟨out,last,?_⟩
      simp only [arrayFromFnLoop,active,↓reduceDIte,call,bind_tc_ok]
      dsimp! only
      rw [add,bind_tc_ok]
      exact run
    · exact ⟨acc.reverse,f,by simp only [arrayFromFnLoop,active,↓reduceDIte]⟩

theorem source {T F : Type} (N : Usize) (cb : core.ops.function.FnMut F Usize T) (f : F)
    (total : ∀ (state : F) (i : Usize), i.val<N.val → ∃ value next,cb.call_mut state i=ok (value,next)) :
    ∃ out, AspisR1SelectedMaskProbe.core.array.from_fn N cb f=ok out := by
  obtain ⟨values,last,run⟩ := loop_total N cb total (N.val+1) 0#usize f [] (by scalar_tac) (by scalar_tac)
  unfold AspisR1SelectedMaskProbe.core.array.from_fn
  rw [run]
  exact ⟨_,rfl⟩

#print axioms loop_total
#print axioms source
end AspisR1.NBA_FromFnTotal
