import NDO_JHl_SumField
import NDO_JHk_LineRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightQueryStep
open Aeneas Aeneas.Std Result AspisR1Stage2
open S7Kani3CallerTrace (Sum PushTrace)
open S7JoinRowsTrace (Progress)
open JHl_SumField (value scalar)

theorem source (i : Fin 10) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (b after : verifier.BatchedWeights) (old : S8OwnedP6Finish.Weights) (sum : Sum)
    (alpha : p.alpha=JFo_Prepared.value.alpha) (next : a.next=JGw_GeometryReads.cursor i)
    (size : a.weights.val.length=64) (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power) (crho : Port3_FlushInstall.Canonical p.rho)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress i.val 0 (Port3_RowsInstall.toBW b))
    (run : Port3_NativeQueryBody.verifier.candidate.query_values JHa_AllQueries.ops
      JFx_NativeBytes.proof p a JFr_TX2_Powers.value none
      (JGp_Geometry.value () JGp_Seeds.geometry) b=ok (.Ok (out,after))) :
    ∃ (o : Port4C_QueryValues.Observation JHa_AllQueries.ops JFx_NativeBytes.proof p a out
      JFr_TX2_Powers.value none (JGp_Geometry.value () JGp_Seeds.geometry) b after), ∃ sumOut,
      PushTrace old (Port3_RowsInstall.toBW after) sumOut ∧
      Progress (i.val+1) 0 (Port3_RowsInstall.toBW after) ∧
      ∀ j : Fin 64,value sumOut j.val=value sum j.val+CheckpointBytes5Output.ofK a.power*
        scalar (AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode o.node) j.val) := by
  obtain ⟨o,line,canon⟩ := JHk_LineRead.source i p a out b after alpha next run
  obtain ⟨basis,out1,after1,sumOut,meaning,call,weights,inc,cr,cp,trace,progress,sums⟩ :=
    JHl_AccumulateSums.source (JGc_TX2_QueryDictionary.input JGp_Seeds.query) p old a b sum i.val
      o.node o.value size (by rw [next];change i.val≤22;omega) (by omega)
      crhs cpower crho canon history phase
  have same := Result.ok.inj (call.symm.trans o.accumulate)
  have ea : out1=out := congrArg Prod.fst same
  have eb : after1=after := congrArg Prod.snd same
  subst out1 after1
  refine ⟨o,sumOut,trace,progress,?_⟩
  intro j
  rw [JHl_SumField.step sum sumOut j a.power basis sums,meaning j]
#print axioms source
end AspisR1.JHl_WeightQueryStep
end
