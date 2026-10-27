import RPv_FJm_LibraStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraSomeCut
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)

theorem reached (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter cursor : FIo_RangeNext.Range)
    (weights : Weights) (side : Usize) (result : ControlFlow FJm_LibraStages.State Weights)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some side,cursor))
    (run : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=ok result) :
    ∃ (base high : Array NQ 4#usize) (q4 q16 : NQ)
      (low : NE) (i0 i1 i2 i3 : Usize) (t0 t1 t2 t3 first2 first3 all : NE),
      FJm_LibraStages.powers extra side=ok (base,high,q4,q16) ∧
      FIo_Native.weights.Weights.scalar_factor base ap0=ok low ∧
      FJm_LibraStages.term ap1 high 0#usize=ok (i0,t0) ∧
      FJm_LibraStages.term ap1 high 1#usize=ok (i1,t1) ∧
      FJm_LibraStages.term ap1 high 2#usize=ok (i2,t2) ∧
      FJm_LibraStages.term ap1 high 3#usize=ok (i3,t3) ∧
      FJm_LibraStages.totals (Array.make 4#usize [t0,t1,t2,t3])=ok (first2,first3,all) ∧
      FJm_LibraStages.finish side low i3 first2 first3 all q4 q16 ap1 weights cursor=
        ok result := by
  unfold FIo_Native.weights.factored_s2_libra_weights_loop.body at run
  rw [hn] at run
  simp only [bind_tc_ok] at run
  obtain ⟨q,h_q,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,h_q1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,h_q2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q3,h_q3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨ignored,h_ignored,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨read2,h_read2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q4,h_q4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q8,h_q8,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q12,h_q12,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q16,h_q16,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨low,h_low,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i0,h_i0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we0,h_we0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨tq0,h_tq0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨prod0,h_prod0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨t0,h_t0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i1,h_i1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we1,h_we1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨tq1,h_tq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨prod1,h_prod1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨t1,h_t1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i2,h_i2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we2,h_we2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨tq2,h_tq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨prod2,h_prod2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨t2,h_t2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i3,h_i3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we3,h_we3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨tq3,h_tq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨prod3,h_prod3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨t3,h_t3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r0,h_r0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r1,h_r1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨first2,h_first2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r2,h_r2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨first3,h_first3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r3,h_r3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨all,h_all,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have tail : FJm_LibraStages.finish side low i3 first2 first3 all q4 q16 ap1 weights cursor=
      ok result := run
  refine ⟨Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q1,q2,q3],
    Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q4,q8,q12],q4,q16,
    low,i0,i1,i2,i3,t0,t1,t2,t3,first2,first3,all,?_,h_low,?_,?_,?_,?_,?_,tail⟩
  · simp only [FJm_LibraStages.powers,h_q,h_q1,h_q2,h_q3,h_ignored,h_read2,h_q4,h_q8,h_q12,h_q16,bind_tc_ok]
  · simp only [FJm_LibraStages.term,h_i0,h_we0,h_tq0,h_prod0,h_t0,bind_tc_ok]
  · simp only [FJm_LibraStages.term,h_i1,h_we1,h_tq1,h_prod1,h_t1,bind_tc_ok]
  · simp only [FJm_LibraStages.term,h_i2,h_we2,h_tq2,h_prod2,h_t2,bind_tc_ok]
  · simp only [FJm_LibraStages.term,h_i3,h_we3,h_tq3,h_prod3,h_t3,bind_tc_ok]
  · simp only [FJm_LibraStages.totals,h_r0,h_r1,h_first2,h_r2,h_first3,h_r3,h_all,bind_tc_ok]
#print axioms reached
end AspisR1.FJm_LibraSomeCut
end
