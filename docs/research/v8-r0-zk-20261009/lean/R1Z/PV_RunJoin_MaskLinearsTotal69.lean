import R1Z.PV_RunJoin_MaskFieldTotal69
import R1Z.PV_RunJoin_SamplerCounters54
import R1Z.ProverRwP6ArrayRead
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskLinearsTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_RunJoin_MaskFieldTotal69

theorem finite (point : Array Q 10#usize) (suffix weighted : Q)
    (n : Nat) (i : Usize) (hi : i.val=n) (bound : n≤10) :
    ∃ out,host_arithmetic.selected_mask_linears_loop point suffix weighted i=ok out := by
  induction n generalizing suffix weighted i with
  | zero =>
    have stop : ¬i>0#usize := by change ¬i.val>0;omega
    unfold host_arithmetic.selected_mask_linears_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_arithmetic.selected_mask_linears_loop.body,stop,if_false,bind_tc_ok]
    exact ⟨_,rfl⟩
  | succ n ih =>
    have more : i>0#usize := by change i.val>0;omega
    have dec : (Usize.wrapping_sub i 1#usize).val=n := by
      rw [PV_RunJoin_SamplerCounters54.sub_one i (by omega)];omega
    obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read point (Usize.wrapping_sub i 1#usize) (by rw [dec];omega)
    obtain ⟨suffix1,hs⟩ := qadd suffix q
    obtain ⟨weighted1,hw⟩ := qadd weighted suffix1
    obtain ⟨outA,ha⟩ := ih suffix1 weighted1 (Usize.wrapping_sub i 1#usize) dec (by omega)
    obtain ⟨outB,hb⟩ := ih suffix1 weighted (Usize.wrapping_sub i 1#usize) dec (by omega)
    unfold host_arithmetic.selected_mask_linears_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_arithmetic.selected_mask_linears_loop.body,more,if_true,lift,hq,hs,bind_tc_ok]
    split
    · exact ⟨outA,by simp only [hw,bind_tc_ok];exact ha⟩
    · exact ⟨outB,hb⟩

theorem complete (point : Array Q 10#usize) :
    ∃ out,host_arithmetic.selected_mask_linears point=ok out := by
  obtain ⟨⟨suffix,weighted⟩,hfirst⟩ := finite point aspis_core.field.QM31.ZERO aspis_core.field.QM31.ZERO
    10 aspis_core.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS rfl (by omega)
  obtain ⟨q,hq⟩ := qscale suffix 3#u32
  obtain ⟨q1,hq1⟩ := qscale weighted 22#u32
  obtain ⟨q2,hq2⟩ := qadd q q1
  obtain ⟨q3,hq3⟩ := qscale suffix 275#u32
  obtain ⟨q4,hq4⟩ := qscale weighted 150#u32
  obtain ⟨q5,hq5⟩ := qadd q3 q4
  exact ⟨(q2,q5),by simp only [host_arithmetic.selected_mask_linears,
    hfirst,hq,hq1,hq2,hq3,hq4,hq5,bind_tc_ok]⟩

#print axioms finite
#print axioms complete
end R1Z.PV_RunJoin_MaskLinearsTotal69
