import R1Z.PV_RunJoin_MultilinearBits69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearSuffix69
open Aeneas Aeneas.Std Result PV_B3_Copy_222 PV_RunJoin_MultilinearField69

theorem complete (point : Array Q 10#usize) (start n : Nat) (coordinate suffix : Usize)
    (rank : coordinate.val+n=10) (lower : start≤coordinate.val)
    (small : suffix.val<2^(coordinate.val-start)) :
    ∃ out,host_multilinear.sparse_eq_weights_loop1 point suffix coordinate=ok out ∧
      out.val<2^(10-start) := by
  induction n generalizing coordinate suffix with
  | zero =>
    have stop : ¬coordinate<10#usize := by change ¬coordinate.val<10;omega
    refine ⟨suffix,?_,by simpa only [show coordinate.val=10 by omega] using small⟩
    unfold host_multilinear.sparse_eq_weights_loop1
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.sparse_eq_weights_loop1.body,stop,if_false,bind_tc_ok]
  | succ n ih =>
    have more : coordinate<10#usize := by change coordinate.val<10;omega
    obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read point coordinate more
    obtain ⟨b,hb⟩ := PV_RunJoin_MultilinearField69.eq q aspis_core.field.QM31.ONE
    let next := (Usize.wrapping_shl suffix 1#u32) ||| core.convert.num.FromUsizeBool.from b
    have inc := PV_RunJoin_SamplerCounters54.increment coordinate (by change coordinate.val<32;omega)
    have nextsmall : next.val<2^((Usize.wrapping_add coordinate 1#usize).val-start) := by
      rw [inc,show coordinate.val+1-start=(coordinate.val-start)+1 by omega]
      exact PV_RunJoin_MultilinearBits69.append_bound suffix b _ small
    obtain ⟨out,ho,hbound⟩ := ih (Usize.wrapping_add coordinate 1#usize) next
      (by rw [inc];omega) (by rw [inc];omega) nextsmall
    refine ⟨out,?_,hbound⟩
    unfold host_multilinear.sparse_eq_weights_loop1
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.sparse_eq_weights_loop1.body,more,if_true,lift,hq,hb,bind_tc_ok]
    exact ho

#print axioms complete
end R1Z.PV_RunJoin_MultilinearSuffix69
