import Port4C_SumField

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_QueryState
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open CheckpointBytes5Output (ofK ofE)
open S7Kani3CallerTrace (Sum PushTrace)
open S7JoinRowsTrace (Progress)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E

def state (a : verifier.Accumulator) (sum : Sum) : QueryAccumulator.State FK FE :=
  ⟨fun i => Port4C_SumField.weight sum i.val,ofE a.rhs,ofK a.power,a.next.val⟩

/-- Complete current source query refines the accumulator step at its actual
observed line-fold value and actual T2 node. The delayed physical weights
are interpreted by the source-derived raw sum, and identified at flush. -/
theorem observed_step (ops : Ops) (basisBackend : Port4C_BasisOuter.SessionABasis ops)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends ops)
    (old : S8OwnedP6Finish.Weights) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (sum : Sum) (t : Nat)
    (size : a.weights.val.length=64) (termBound : t<22)
    (hp : Port3_FlushInstall.Canonical a.power) (hrho : Port3_FlushInstall.Canonical p.rho)
    (hrhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (lineCanonical : ∀ alpha values inverses value,
      ops.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress t 0 (Port3_RowsInstall.toBW b))
    (h : verifier.candidate.query_values (Port4C_RowStd.install ops)
      proof p a g obs geometry b=ok (.Ok (out,bout))) :
    ∃ (o : Port4C_QueryValues.Observation (Port4C_RowStd.install ops)
      proof p a out g obs geometry b bout) (sumOut : Sum),
      PushTrace old (Port3_RowsInstall.toBW bout) sumOut ∧
      Progress (t+1) 0 (Port3_RowsInstall.toBW bout) ∧
      state out sumOut=QueryAccumulator.step LiteralOpeningView.eK (ofK p.rho)
        (fun _ => ofE o.value)
        (fun _ i => Port4C_SumField.scalar
          (AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode o.node) i.val))
        (state a sum) := by
  obtain ⟨o,sumOut,trace,progress,sums,rhs,power,next,_,_,_⟩ := Port4C_QueryMeaning.query
    ops basisBackend arithmetic old proof p a out g obs geometry b bout sum t size termBound
    hp hrho hrhs lineCanonical history phase h
  refine ⟨o,sumOut,trace,progress,?_⟩
  unfold state QueryAccumulator.step
  congr 1
  · funext i
    exact Port4C_SumField.update sum sumOut a.power _ sums i
  · exact rhs
  · exact power
  · exact next

#print axioms observed_step
end AspisR1.Port4C_QueryState
end
