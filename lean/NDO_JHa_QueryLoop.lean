import NDO_JHa_AllQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_QueryLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
abbrev ops := JHa_AllQueries.ops

def Post (old : S8OwnedP6Finish.Weights) (weights : alloc.vec.Vec aspis_core.field.QM31)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop :=
  a.weights=weights ∧ a.next.val=10 ∧
  Port4C_QueryArithmetic.CanonE a.rhs ∧ Port3_FlushInstall.Canonical a.power ∧
  ∃ sum, PushTrace old (Port3_RowsInstall.toBW b) sum ∧ Progress 10 0 (Port3_RowsInstall.toBW b)

theorem suffix (p : verifier.Prepared) (old : S8OwnedP6Finish.Weights)
    (queries : p.queries=JFq_Queries.value) (alpha : p.alpha=JFo_Prepared.value.alpha)
    (crho : Port3_FlushInstall.Canonical p.rho) (k : Nat)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (sum : Sum)
    (remaining : a.next.val+k=10) (size : a.weights.val.length=64)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress a.next.val 0 (Port3_RowsInstall.toBW b)) :
    ∃ out after,
      Port3_NativeQueryBody.verifier.candidate.query_loop_loop ops (.Ok (a,b)) JFx_NativeBytes.proof p JFr_TX2_Powers.value none
        (JGp_Geometry.value () JGp_Seeds.geometry) 10#usize=ok (.Ok (out,after)) ∧
      Post old a.weights out after := by
  induction k generalizing a b sum with
  | zero =>
    have ending : a.next.val=10 := by omega
    refine ⟨a,b,?_,rfl,ending,crhs,cpower,sum,history,?_⟩
    · unfold Port3_NativeQueryBody.verifier.candidate.query_loop_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,Aeneas.Std.uncurry,if_pos (show a.next≥10#usize from by change a.next.val≥10;omega),bind_tc_ok]
    · simpa only [ending] using phase
  | succ k ih =>
    have active : a.next.val<10 := by omega
    let i : Fin 10 := ⟨a.next.val,active⟩
    have cursor : a.next=JGw_GeometryReads.cursor i := by
      apply UScalar.eq_of_val_eq
      rfl
    obtain ⟨middle,pending,sum1,step,weights,next,cr,cp,ht,hp⟩ :=
      JHa_AllQueries.source i p a b old sum queries alpha cursor size crhs cpower crho history phase
    have left : middle.next.val+k=10 := by change middle.next.val=a.next.val+1 at next;omega
    obtain ⟨out,after,tail,post⟩ := ih middle pending sum1 left (by rw [weights];exact size) cr cp ht
      (by rw [next];exact hp)
    refine ⟨out,after,?_,?_⟩
    · unfold Port3_NativeQueryBody.verifier.candidate.query_loop_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,
        Aeneas.Std.uncurry,if_neg (show ¬a.next≥10#usize from by change ¬a.next.val≥10;omega),step,bind_tc_ok]
      exact tail
    · simpa only [weights] using post
#print axioms suffix
end AspisR1.JHa_QueryLoop
end
