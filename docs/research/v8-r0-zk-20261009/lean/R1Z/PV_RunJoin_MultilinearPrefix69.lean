import R1Z.PV_RunJoin_MultilinearField69
import R1Z.PV_RunJoin_SamplerCounters54
import R1Z.ProverRwP6ArrayRead
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearPrefix69
open Aeneas Aeneas.Std Result PV_B3_Copy_222 PV_RunJoin_MultilinearField69

theorem complete (point : Array Q 10#usize) (n : Nat) (i : Usize)
    (hi : i.val=n) (bound : n≤10) :
    ∃ out,host_multilinear.sparse_eq_weights_loop0 point i=ok out ∧ out.val≤n := by
  induction n generalizing i with
  | zero =>
    have stop : ¬i>0#usize := by change ¬i.val>0;omega
    refine ⟨i,?_,by omega⟩
    unfold host_multilinear.sparse_eq_weights_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.sparse_eq_weights_loop0.body,stop,if_false,bind_tc_ok]
  | succ n ih =>
    have more : i>0#usize := by change i.val>0;omega
    have dec : (Usize.wrapping_sub i 1#usize).val=n := by
      rw [PV_RunJoin_SamplerCounters54.sub_one i (by omega)];omega
    obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read point (Usize.wrapping_sub i 1#usize)
      (by change (Usize.wrapping_sub i 1#usize).val<10;rw [dec];omega)
    obtain ⟨b,hb⟩ := PV_RunJoin_MultilinearField69.eq q aspis_core.field.QM31.ZERO
    obtain ⟨b1,hb1⟩ := PV_RunJoin_MultilinearField69.eq q aspis_core.field.QM31.ONE
    obtain ⟨out,ho,hbound⟩ := ih (Usize.wrapping_sub i 1#usize) dec (by omega)
    have expand : host_multilinear.sparse_eq_weights_loop0 point i=
      if b then host_multilinear.sparse_eq_weights_loop0 point (Usize.wrapping_sub i 1#usize)
      else if b1 then host_multilinear.sparse_eq_weights_loop0 point (Usize.wrapping_sub i 1#usize)
      else ok i := by
      conv_lhs => unfold host_multilinear.sparse_eq_weights_loop0
      rw [ProverRw19LoopBind.loop_bind]
      simp only [host_multilinear.sparse_eq_weights_loop0.body,more,if_true,lift,hq,hb,hb1,bind_tc_ok]
      cases b <;> cases b1 <;> rfl
    rw [expand]
    cases b <;> cases b1 <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact ⟨i,rfl,by omega⟩
    all_goals exact ⟨out,ho,by omega⟩

#print axioms complete
end R1Z.PV_RunJoin_MultilinearPrefix69
