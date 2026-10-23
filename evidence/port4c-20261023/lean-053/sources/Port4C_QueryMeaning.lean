import Port4C_Accumulation
import Port4C_QueryArithmetic

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_QueryMeaning
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_RowsInstall (toK toBW)
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
open CheckpointBytes5Output (ofK ofE)

private theorem canonical (q : aspis_core.field.QM31) (h : Port3_FlushInstall.Canonical q) :
    S7JoinBackendCarriers.Canonical (toK q) := by
  intro k
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

private theorem arithmetic_std (ops : Ops) (backend : Port4C_QueryArithmetic.SessionABackends ops) :
    Port4C_QueryArithmetic.SessionABackends (Port4C_RowStd.install ops) :=
  ⟨backend.s3_s4_s5_mulE,backend.s3_s4_s5_addE,backend.s3_s4_s9_mulK⟩

/-- CURRENT query opening/folds, native six-level basis, all64 row writes,
terms, rhs/power/next and canonicality from one accepted source call.
The actual folded value/node are retained for later parsed/frozen2 binding. -/
theorem query (ops : Ops) (basisBackend : Port4C_BasisOuter.SessionABasis ops)
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
    (history : PushTrace old (toBW b) sum) (phase : Progress t 0 (toBW b))
    (h : verifier.candidate.query_values (Port4C_RowStd.install ops)
      proof p a g obs geometry b=ok (.Ok (out,bout))) :
    ∃ (o : Port4C_QueryValues.Observation (Port4C_RowStd.install ops)
        proof p a out g obs geometry b bout) (sumOut : Sum),
      PushTrace old (toBW bout) sumOut ∧ Progress (t+1) 0 (toBW bout) ∧
      (∀ i, i<64 → ∀ k : Fin 4,
        (sumOut i k : ZMod AspisCircleGroupOrder.P)=(sum i k : ZMod AspisCircleGroupOrder.P)+
          (S7Kani2OwnedRowRefinement.powerLimb (toK a.power) k).val*
            AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode o.node) i) ∧
      ofE out.rhs=ofE a.rhs+LiteralOpeningView.eK (ofK a.power)*ofE o.value ∧
      ofK out.power=ofK a.power*ofK p.rho ∧ out.next.val=a.next.val+1 ∧
      out.weights=a.weights ∧ Port4C_QueryArithmetic.CanonE out.rhs ∧
      Port3_FlushInstall.Canonical out.power := by
  obtain ⟨o⟩ := Port4C_QueryValues.observed (Port4C_RowStd.install ops)
    proof p a out g obs geometry b bout h
  have frame := Port3_NativeQueryFrame.query_fields (Port4C_RowStd.install ops)
    proof p a out g obs geometry b bout h
  obtain ⟨sumOut,trace,progress,sums⟩ := Port4C_Accumulation.rows ops basisBackend old p a out b bout
    o.node o.value sum t size (by omega) termBound (canonical a.power hp) history phase o.accumulate
  have fields := Port4C_QueryArithmetic.accumulation (Port4C_RowStd.install ops)
    (arithmetic_std ops arithmetic) p a out o.node o.value b bout hp hrho hrhs
    (lineCanonical o.alpha1 o.values o.inverse o.value o.line) o.accumulate
  exact ⟨o,sumOut,trace,progress,sums,fields.1,fields.2.1,frame.2.2,frame.2.1,fields.2.2⟩

#print axioms canonical
#print axioms arithmetic_std
#print axioms query
end AspisR1.Port4C_QueryMeaning
end
