import NDO_JHk_QueryPowerLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_QueryPowerTen
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
open CheckpointBytes5Output (ofK)

theorem source (p : verifier.Prepared) (old : S8OwnedP6Finish.Weights)
    (queries : p.queries=JFq_Queries.value) (alpha : p.alpha=JFo_Prepared.value.alpha)
    (crho : Port3_FlushInstall.Canonical p.rho)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (sum : Sum)
    (zero : a.next=0#usize) (size : a.weights.val.length=64)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress 0 0 (Port3_RowsInstall.toBW b))
    (out : verifier.Accumulator) (after : verifier.BatchedWeights)
    (run : Port3_NativeQueryBody.verifier.candidate.query_loop_loop JHa_QueryLoop.ops (.Ok (a,b))
      JFx_NativeBytes.proof p JFr_TX2_Powers.value none
      (JGp_Geometry.value () JGp_Seeds.geometry) 10#usize=ok (.Ok (out,after))) :
    ofK out.power=ofK a.power*ofK p.rho^10 := by
  exact JHk_QueryPowerLoop.source p old queries alpha crho 10 a b sum
    (by rw [zero];rfl) size crhs cpower history (by rw [zero];exact phase) out after run
#print axioms source
end AspisR1.JHk_QueryPowerTen
end
