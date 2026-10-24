import Port4C_FlushState
import OraclePortCheckpointResumeC5
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Advance
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_RowsInstall (toBW)
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
open CheckpointBytes5Output (ofK ofE)
abbrev Model := OraclePortCheckpointStateC3.Prepared Port4C_QueryState.FK Port4C_QueryState.FE

theorem advance_first (model : Model) (n : Nat) (s : QueryAccumulator.State Port4C_QueryState.FK Port4C_QueryState.FE) :
    OraclePortCheckpointStateC3.advance model n
      (QueryAccumulator.step model.iota model.rho (QueryAccumulator.extend22 model.values)
        (QueryAccumulator.extend22 model.basis) s)=
    OraclePortCheckpointStateC3.advance model (n+1) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold OraclePortCheckpointStateC3.advance
    rw [ih]

/-- A local interpretation on the actual observations, used by the generic
Calls induction. Its concrete construction is the parsed/opening/geometry port,
not an additional successful query or a whole-loop equality. -/
def Binds (model : Model) (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (a out : verifier.Accumulator)
    (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install ops) proof p a out g obs geometry b bout) : Prop :=
  ofE o.value=QueryAccumulator.extend22 model.values a.next.val ∧
    ∀ i : Fin 64, Port4C_SumField.scalar
      (AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode o.node) i.val)=
      QueryAccumulator.extend22 model.basis a.next.val i

/-- Symbolic induction over the ACTUAL source Calls, carrying the source's
own PushTrace/phase and the exact virtual four-field state. -/
theorem calls (ops : Ops) (basisBackend : Port4C_BasisOuter.SessionABasis ops)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends ops) (model : Model)
    (embedding : model.iota=LiteralOpeningView.eK)
    (old : S8OwnedP6Finish.Weights) (proof : Slice U8) (p : verifier.Prepared)
    (rho : model.rho=ofK p.rho)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (end1 : Nat)
    (binding : ∀ a out b bout,
      verifier.candidate.query_values (Port4C_RowStd.install ops) proof p a g obs geometry b=ok (.Ok (out,bout)) →
      ∀ o : Port4C_QueryValues.Observation (Port4C_RowStd.install ops) proof p a out g obs geometry b bout,
        Binds model ops proof p g obs geometry a out b bout o)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights) (n t : Nat) (sum : Sum)
    (size : a.weights.val.length=64) (limit : t+n≤22)
    (hp : Port3_FlushInstall.Canonical a.power) (hrho : Port3_FlushInstall.Canonical p.rho)
    (hrhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (lineCanonical : ∀ alpha values inverses value,
      ops.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    (history : PushTrace old (toBW b) sum) (phase : Progress t 0 (toBW b))
    (actual : Port2_QueryLoop.Calls
      (fun a b => verifier.candidate.query_values (Port4C_RowStd.install ops)
        proof p a g obs geometry b) end1 a b out bout n) :
    ∃ sumOut, PushTrace old (toBW bout) sumOut ∧ Progress (t+n) 0 (toBW bout) ∧
      Port4C_QueryState.state out sumOut=
        OraclePortCheckpointStateC3.advance model n (Port4C_QueryState.state a sum) ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power := by
  induction actual generalizing t sum with
  | done => exact ⟨sum,history,by simpa only [Nat.add_zero] using phase,rfl,hrhs,hp⟩
  | @step a a1 out b b1 bout n active returned tail ih =>
    obtain ⟨o,sum1,trace,progress,stateStep⟩ := Port4C_QueryState.observed_step ops basisBackend arithmetic
      old proof p a a1 g obs geometry b b1 sum t size (by omega) hp hrho hrhs lineCanonical history phase returned
    obtain ⟨_,_,_,_,_,_,_,_,weights,canonRhs,canonPower⟩ :=
      Port4C_QueryMeaning.query ops basisBackend arithmetic old proof p a a1 g obs geometry b b1 sum t
        size (by omega) hp hrho hrhs lineCanonical history phase returned
    have meaning := binding a a1 b b1 returned o
    have stepEq : Port4C_QueryState.state a1 sum1=
        QueryAccumulator.step model.iota model.rho (QueryAccumulator.extend22 model.values)
          (QueryAccumulator.extend22 model.basis) (Port4C_QueryState.state a sum) := by
      rw [stateStep]
      unfold QueryAccumulator.step
      rw [embedding,rho]
      congr 1
      · funext i
        rw [meaning.2 i]
      · rw [meaning.1]
    obtain ⟨sumOut,traceOut,progressOut,stateOut,canonRhsOut,canonPowerOut⟩ :=
      ih (t+1) sum1 (by rw [weights]; exact size) (by omega) canonPower canonRhs trace progress
    refine ⟨sumOut,traceOut,?_,?_,canonRhsOut,canonPowerOut⟩
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using progressOut
    · rw [stateOut,stepEq,advance_first]

#print axioms advance_first
#print axioms calls
end AspisR1.Port5Q1_Advance
end
