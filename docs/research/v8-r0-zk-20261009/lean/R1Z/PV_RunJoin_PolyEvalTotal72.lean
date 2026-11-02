import R1Z.PV_RunJoin_PolyBlockTotal72
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PolyEvalTotal72
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_RunJoin_MaskFieldTotal69

theorem loop (polynomial : Array Q 28#usize) (powers : Array Q 3#usize)
    (prepared : host_arithmetic.PreparedQm31Multiplier) (accumulator : Q)
    (n : Nat) (block : Usize) (rank : block.val=n) (bound : n≤6) :
    ∃ out,host_arithmetic.evaluate_state_only_polynomial_loop polynomial powers prepared accumulator block=ok out := by
  induction n generalizing block accumulator with
  | zero =>
    have stop : ¬block>0#usize := by change ¬block.val>0;omega
    unfold host_arithmetic.evaluate_state_only_polynomial_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_arithmetic.evaluate_state_only_polynomial_loop.body,stop,if_false,bind_tc_ok]
    exact ⟨accumulator,rfl⟩
  | succ n ih =>
    have more : block>0#usize := by change block.val>0;omega
    have pred := PV_B3_PrefixRank222.decrement block more
    obtain ⟨q,hq⟩ := PV_RunJoin_MaskPreparedTotal69.mul prepared accumulator
    obtain ⟨q1,hq1⟩ := PV_RunJoin_PolyBlockTotal72.complete polynomial powers (Usize.wrapping_sub block 1#usize) (by rw [pred];omega)
    obtain ⟨next,hn⟩ := qadd q q1
    obtain ⟨out,ho⟩ := ih next (Usize.wrapping_sub block 1#usize) (by rw [pred];omega) (by omega)
    refine ⟨out,?_⟩
    unfold host_arithmetic.evaluate_state_only_polynomial_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_arithmetic.evaluate_state_only_polynomial_loop.body,more,if_true,
      lift,bind_tc_ok,hq,hq1,hn,Aeneas.Std.uncurry]
    exact ho

theorem complete (polynomial : Array Q 28#usize) (challenge : Q) :
    ∃ out,host_arithmetic.evaluate_state_only_polynomial polynomial challenge=ok out := by
  obtain ⟨x2,h2⟩ := qsquare challenge
  obtain ⟨x3,h3⟩ := qmul challenge x2
  obtain ⟨x4,h4⟩ := qsquare x2
  obtain ⟨prepared,hp⟩ := PV_RunJoin_MaskPreparedTotal69.prepare x4
  obtain ⟨accumulator,ha⟩ := PV_RunJoin_PolyBlockTotal72.complete polynomial
    (Array.make 3#usize [challenge,x2,x3]) 6#usize (by decide)
  obtain ⟨out,ho⟩ := loop polynomial (Array.make 3#usize [challenge,x2,x3]) prepared accumulator 6 6#usize rfl (by decide)
  exact ⟨out,by simp only [host_arithmetic.evaluate_state_only_polynomial,h2,h3,h4,hp,ha,ho,bind_tc_ok]⟩

#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_PolyEvalTotal72
