import Port4C_FlushState

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_Advance
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open CheckpointBytes5Output (ofK ofE)
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
open Port4C_QueryState (state FK FE)

/-- LOCAL source-binding frontier. It describes only the actual observed line
value and node at the source index, not the result of a query or loop. The
concrete parsed/frozen2 instance must come from opening/geometry refinement. -/
structure ObservationBinding (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry)
    (m : OraclePortCheckpointStateC3.Prepared FK FE) : Prop where
  iota : m.iota=LiteralOpeningView.eK
  rho : m.rho=ofK p.rho
  value : ∀ a out b bout
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install ops)
      proof p a out g obs geometry b bout),
    ofE o.value=QueryAccumulator.extend22 m.values a.next.val
  basis : ∀ a out b bout
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install ops)
      proof p a out g obs geometry b bout) (i : Fin 64),
    Port4C_SumField.scalar
      (AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode o.node) i.val)=
      QueryAccumulator.extend22 m.basis a.next.val i

theorem advance_step (m : OraclePortCheckpointStateC3.Prepared FK FE)
    (n : Nat) (s : QueryAccumulator.State FK FE) :
    OraclePortCheckpointStateC3.advance m n
      (QueryAccumulator.step m.iota m.rho (QueryAccumulator.extend22 m.values)
        (QueryAccumulator.extend22 m.basis) s)=
      OraclePortCheckpointStateC3.advance m (n+1) s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [OraclePortCheckpointStateC3.advance,ih]; rfl

/-- Arithmetic induction over the SAME native calls. Canonicality and the
source push trace propagate internally. No ten-step result is a premise. -/
theorem calls (ops : Ops) (basisBackend : Port4C_BasisOuter.SessionABasis ops)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends ops)
    (old : S8OwnedP6Finish.Weights) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (end1 : Nat)
    (m : OraclePortCheckpointStateC3.Prepared FK FE)
    (binding : ObservationBinding ops proof p g obs geometry m)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (n t : Nat) (sum : Sum)
    (size : a.weights.val.length=64) (limit : t+n≤22)
    (hp : Port3_FlushInstall.Canonical a.power) (hrho : Port3_FlushInstall.Canonical p.rho)
    (hrhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (lineCanonical : ∀ alpha values inverses value,
      ops.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress t 0 (Port3_RowsInstall.toBW b))
    (actual : Port2_QueryLoop.Calls
      (fun a b => verifier.candidate.query_values (Port4C_RowStd.install ops)
        proof p a g obs geometry b) end1 a b out bout n) :
    ∃ sumOut, PushTrace old (Port3_RowsInstall.toBW bout) sumOut ∧
      Progress (t+n) 0 (Port3_RowsInstall.toBW bout) ∧
      state out sumOut=OraclePortCheckpointStateC3.advance m n (state a sum) := by
  induction actual generalizing t sum with
  | done => exact ⟨sum,history,by simpa only [Nat.add_zero] using phase,rfl⟩
  | @step a a1 out b b1 bout n active returned tail ih =>
    obtain ⟨o,sum1,trace,progress,observed⟩ := Port4C_QueryState.observed_step
      ops basisBackend arithmetic old proof p a a1 g obs geometry b b1 sum t size
      (by omega) hp hrho hrhs lineCanonical history phase returned
    have frame := Port3_NativeQueryFrame.query_fields (Port4C_RowStd.install ops)
      proof p a a1 g obs geometry b b1 returned
    have canonical := Port4C_QueryArithmetic.accumulation (Port4C_RowStd.install ops)
      ⟨arithmetic.s3_s4_s5_mulE,arithmetic.s3_s4_s5_addE,arithmetic.s3_s4_s9_mulK⟩
      p a a1 o.node o.value b b1 hp hrho hrhs
      (lineCanonical o.alpha1 o.values o.inverse o.value o.line) o.accumulate
    obtain ⟨sumOut,traceOut,progressOut,meaning⟩ := ih (t+1) sum1
      (by rw [frame.2.1]; exact size) (by omega) canonical.2.2.2
      canonical.2.2.1 trace progress
    have step : state a1 sum1=QueryAccumulator.step m.iota m.rho
        (QueryAccumulator.extend22 m.values) (QueryAccumulator.extend22 m.basis) (state a sum) := by
      rw [observed,binding.iota,binding.rho]
      unfold QueryAccumulator.step state
      congr 1
      · funext i
        rw [binding.basis a a1 b b1 o i]
      · rw [binding.value a a1 b b1 o]
    refine ⟨sumOut,traceOut,?_,?_⟩
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using progressOut
    · rw [meaning,step,advance_step]

#print axioms advance_step
#print axioms calls
end AspisR1.Port5Q2_Advance
end
