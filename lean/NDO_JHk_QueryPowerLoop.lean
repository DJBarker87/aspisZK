import NDO_JHk_QueryPowerStep
import NDO_JHa_QueryLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_QueryPowerLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
open CheckpointBytes5Output (ofK)

/-- Strengthens the retained returning suffix with a power projection on
the SAME return. It reuses every inherited query and pending-row proof. -/
theorem source (p : verifier.Prepared) (old : S8OwnedP6Finish.Weights)
    (queries : p.queries=JFq_Queries.value) (alpha : p.alpha=JFo_Prepared.value.alpha)
    (crho : Port3_FlushInstall.Canonical p.rho) (k : Nat)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (sum : Sum)
    (remaining : a.next.val+k=10) (size : a.weights.val.length=64)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress a.next.val 0 (Port3_RowsInstall.toBW b))
    (out : verifier.Accumulator) (after : verifier.BatchedWeights)
    (run : Port3_NativeQueryBody.verifier.candidate.query_loop_loop JHa_QueryLoop.ops (.Ok (a,b))
      JFx_NativeBytes.proof p JFr_TX2_Powers.value none
      (JGp_Geometry.value () JGp_Seeds.geometry) 10#usize=ok (.Ok (out,after))) :
    ofK out.power=ofK a.power*ofK p.rho^k := by
  induction k generalizing a b sum with
  | zero =>
    have ending : a.next.val=10 := by omega
    unfold Port3_NativeQueryBody.verifier.candidate.query_loop_loop at run
    rw [Aeneas.Std.loop.eq_def] at run
    simp only [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,Aeneas.Std.uncurry,
      if_pos (show a.next≥10#usize from by change a.next.val≥10;omega),bind_tc_ok] at run
    have same := congrArg (fun pair => pair.1.power)
      (core.result.Result.Ok.inj (Result.ok.inj run))
    simpa only [pow_zero,mul_one] using congrArg ofK same.symm
  | succ k ih =>
    have active : a.next.val<10 := by omega
    let i : Fin 10 := ⟨a.next.val,active⟩
    have cursor : a.next=JGw_GeometryReads.cursor i := by
      apply UScalar.eq_of_val_eq
      rfl
    obtain ⟨middle,pending,sum1,step,weights,next,cr,cp,ht,hp⟩ :=
      JHa_AllQueries.source i p a b old sum queries alpha cursor size crhs cpower crho history phase
    have power := (JHk_QueryPowerStep.source JGp_Seeds.query _ _ _ _ _ _ _ _ _ cpower crho step).1
    have left : middle.next.val+k=10 := by
      change middle.next.val=a.next.val+1 at next
      omega
    unfold Port3_NativeQueryBody.verifier.candidate.query_loop_loop at run
    rw [Aeneas.Std.loop.eq_def] at run
    simp only [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,Aeneas.Std.uncurry,
      if_neg (show ¬a.next≥10#usize from by change ¬a.next.val≥10;omega),step,bind_tc_ok] at run
    have tail := ih middle pending sum1 left (by rw [weights];exact size) cr cp ht
      (by rw [next];exact hp) run
    rw [tail,power,pow_succ]
    ring
#print axioms source
end AspisR1.JHk_QueryPowerLoop
end
