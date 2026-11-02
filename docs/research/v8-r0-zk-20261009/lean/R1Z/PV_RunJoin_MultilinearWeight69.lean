import R1Z.PV_RunJoin_MultilinearPrefix69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearWeight69
open Aeneas Aeneas.Std Result PV_B3_Copy_222 PV_RunJoin_MultilinearField69

theorem complete (point : Array Q 10#usize) (prefix_len prefix1 : Usize)
    (bound : prefix_len.val≤10) (n : Nat) (coordinate : Usize) (weight : Q)
    (rank : coordinate.val+n=prefix_len.val) :
    ∃ out,host_multilinear.sparse_eq_weights_loop2_loop0 point prefix_len prefix1 weight coordinate=ok out := by
  induction n generalizing coordinate weight with
  | zero =>
    have stop : ¬coordinate<prefix_len := by change ¬coordinate.val<prefix_len.val;omega
    unfold host_multilinear.sparse_eq_weights_loop2_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.sparse_eq_weights_loop2_loop0.body,stop,if_false,bind_tc_ok]
    exact ⟨weight,rfl⟩
  | succ n ih =>
    have more : coordinate<prefix_len := by change coordinate.val<prefix_len.val;omega
    obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read point coordinate (by change coordinate.val<10;omega)
    obtain ⟨qm,hm⟩ := qsub aspis_core.field.QM31.ONE q
    let bit := (Usize.wrapping_shr prefix1 (UScalar.cast .U32
      (Usize.wrapping_sub (Usize.wrapping_sub prefix_len 1#usize) coordinate))) &&& 1#usize
    let factor := if bit=0#usize then qm else q
    have hf : (if bit=0#usize then aspis_core.field.QM31.sub aspis_core.field.QM31.ONE q else ok q)=ok factor := by
      dsimp only [factor];split <;> simp only [hm]
    obtain ⟨next,hn⟩ := qmul weight factor
    have inc := PV_RunJoin_SamplerCounters54.increment coordinate (by change coordinate.val<32;omega)
    obtain ⟨out,ho⟩ := ih (Usize.wrapping_add coordinate 1#usize) next (by rw [inc];omega)
    refine ⟨out,?_⟩
    unfold host_multilinear.sparse_eq_weights_loop2_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.sparse_eq_weights_loop2_loop0.body,more,if_true,lift,hq,bind_tc_ok]
    change (do let q ← (if bit=0#usize then aspis_core.field.QM31.sub aspis_core.field.QM31.ONE q else ok q)
               let w ← aspis_core.field.QM31.mul weight q
               host_multilinear.sparse_eq_weights_loop2_loop0 point prefix_len prefix1 w
                 (Usize.wrapping_add coordinate 1#usize))=ok out
    rw [hf,bind_tc_ok,hn,bind_tc_ok]
    exact ho

#print axioms complete
end R1Z.PV_RunJoin_MultilinearWeight69
