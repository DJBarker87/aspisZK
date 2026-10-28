import NDO_JHk_QueryRhsStep
import NDO_JHa_QueryLoop
import NDO_JHk_QueryPowerStep
import NDO_JHk_RhsFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_QueryRhsLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
open CheckpointBytes5Output (ofE ofK)

/-- Numeric rhs invariant on the SAME inherited native suffix. -/
theorem source (p : verifier.Prepared) (old : S8OwnedP6Finish.Weights)
    (queries : p.queries=JFq_Queries.value) (alpha : p.alpha=JFo_Prepared.value.alpha)
    (rho : p.rho=JFq_Rho.scalar) (crho : Port3_FlushInstall.Canonical p.rho) (k : Nat)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (sum : Sum)
    (remaining : a.next.val+k=10) (size : a.weights.val.length=64)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress a.next.val 0 (Port3_RowsInstall.toBW b))
    (rhs : ofE a.rhs=JHk_RhsFacts.rhs a.next.val)
    (power : ofK a.power=JHk_RhsFacts.power a.next.val)
    (out : verifier.Accumulator) (after : verifier.BatchedWeights)
    (run : Port3_NativeQueryBody.verifier.candidate.query_loop_loop JHa_QueryLoop.ops (.Ok (a,b))
      JFx_NativeBytes.proof p JFr_TX2_Powers.value none
      (JGp_Geometry.value () JGp_Seeds.geometry) 10#usize=ok (.Ok (out,after))) :
    ofE out.rhs=JHk_RhsFacts.rhs 10 := by
  induction k generalizing a b sum with
  | zero =>
    have ending : a.next.val=10 := by omega
    unfold Port3_NativeQueryBody.verifier.candidate.query_loop_loop at run
    rw [Aeneas.Std.loop.eq_def] at run
    simp only [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,Aeneas.Std.uncurry,
      if_pos (show a.next≥10#usize from by change a.next.val≥10;omega),bind_tc_ok] at run
    have same := congrArg Prod.fst (core.result.Result.Ok.inj (Result.ok.inj run))
    change a=out at same
    rw [←same,rhs,ending]
  | succ k ih =>
    have active : a.next.val<10 := by omega
    let i : Fin 10 := ⟨a.next.val,active⟩
    have cursor : a.next=JGw_GeometryReads.cursor i := by
      apply UScalar.eq_of_val_eq
      rfl
    obtain ⟨middle,pending,sum1,step,weights,next,cr,cp,ht,hp⟩ :=
      JHa_AllQueries.source i p a b old sum queries alpha cursor size crhs cpower crho history phase
    have hr := JHk_QueryRhsStep.source i p a middle b pending alpha cursor cpower crho crhs step
    have hq := (JHk_QueryPowerStep.source JGp_Seeds.query _ _ _ _ _ _ _ _ _ cpower crho step).1
    have left : middle.next.val+k=10 := by
      change middle.next.val=a.next.val+1 at next
      omega
    have rhs1 : ofE middle.rhs=JHk_RhsFacts.rhs middle.next.val := by
      rw [hr,rhs,power,←JHk_RhsFacts.rhs_step i,next]
    have power1 : ofK middle.power=JHk_RhsFacts.power middle.next.val := by
      rw [hq,rho,power,←JHk_RhsFacts.power_step i,next]
    unfold Port3_NativeQueryBody.verifier.candidate.query_loop_loop at run
    rw [Aeneas.Std.loop.eq_def] at run
    simp only [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,Aeneas.Std.uncurry,
      if_neg (show ¬a.next≥10#usize from by change ¬a.next.val≥10;omega),step,bind_tc_ok] at run
    exact ih middle pending sum1 left (by rw [weights];exact size) cr cp ht
      (by rw [next];exact hp) rhs1 power1 run
#print axioms source
end AspisR1.JHk_QueryRhsLoop
end
