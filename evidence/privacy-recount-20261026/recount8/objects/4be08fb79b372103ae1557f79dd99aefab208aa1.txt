import R1Z.PV_RunJoin_SampleTailStep34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SampleTail34
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_SampleTailStep34
variable [ExternalTypes]

/-- Complete actual Boolean-tail loop, at every in-range source round.
The decreasing number of remaining coordinates is symbolic, never a
kernel-reduced ten-step source execution. -/
theorem exact_tail (ops : ExternalFuns) (n : Nat) (p : Nat → Raw)
    (r rem a off : Usize) (hr : r.val<10) (hrem : rem.val=9-r.val)
    (bound : off.val+n=rem.val) :
    @host_sumcheck.evaluate_assignment_loop _ (ProverRwDictionaryScalar.selected ops)
      r rem a (PV_RunJoin_PointArray34.array p) off =
    .ok (PV_RunJoin_PointArray34.array
      (ProverCommitSampleTail49.values n p r.val rem.val a off.val)) := by
  induction n generalizing p off with
  | zero =>
    have hn : ¬off<rem := by change ¬off.val<rem.val; omega
    unfold host_sumcheck.evaluate_assignment_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_sumcheck.evaluate_assignment_loop.body,hn,if_false,bind_tc_ok,
      ProverCommitSampleTail49.values]
  | succ n ih =>
    have ho : off.val<rem.val := by omega
    have inc := increment off (by omega)
    unfold host_sumcheck.evaluate_assignment_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [step ops p r rem a off hr hrem ho]
    simp only [bind_tc_ok]
    change @host_sumcheck.evaluate_assignment_loop _ (ProverRwDictionaryScalar.selected ops)
      r rem a (PV_RunJoin_PointArray34.array _) (Usize.wrapping_add off 1#usize) = _
    rw [ih _ _ (by rw [inc];omega)]
    simp only [ProverCommitSampleTail49.values,inc]

#print axioms exact_tail
end R1Z.PV_RunJoin_SampleTail34
