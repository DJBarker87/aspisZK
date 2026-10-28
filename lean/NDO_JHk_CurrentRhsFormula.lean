import NDO_JHk_QueryRhsLoop
import NDO_JHk_CurrentQuery
import NDO_JHk_PowerInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_CurrentRhsFormula
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open CheckpointBytes5Output (ofE ofK)

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (queries : p.queries=JFq_Queries.value)
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) :
    ofE (Tx1Q_Carriers.accumulator out).rhs=ofE JFq_Rhs.scalar := by
  obtain ⟨alpha,rho,powers,geometry⟩ := JHk_PowerInputs.source p input scratch g prepare queries geo
  obtain ⟨size,zero,crhs,cpower,history,phase⟩ := JHa_Pending.source initial pending init pend
  have crho : Port3_FlushInstall.Canonical (Tx1Q_Carriers.prepared p).rho := by
    rw [rho]
    exact JFn_AccumulatorCanonical.rho
  have native := JHk_CurrentQuery.source p initial out scratch g pending after query
  rw [powers,geometry] at native
  have initialFacts := JGw_InitialFacts.source initial init
  have rhs0 : ofE (Tx1Q_Carriers.accumulator initial).rhs=
      JHk_RhsFacts.rhs (Tx1Q_Carriers.accumulator initial).next.val := by
    rw [initialFacts.2.1,zero]
    rfl
  have power0 : ofK (Tx1Q_Carriers.accumulator initial).power=
      JHk_RhsFacts.power (Tx1Q_Carriers.accumulator initial).next.val := by
    rw [initialFacts.2.2.1,zero]
    rfl
  have rhs := JHk_QueryRhsLoop.source (Tx1Q_Carriers.prepared p)
    (Port3_PendingInstall.owned (Tx1Q_Carriers.accumulator initial).weights.deref)
    queries alpha rho crho 10 (Tx1Q_Carriers.accumulator initial) (Tx1Q_Carriers.pending pending)
    _ (by rw [zero];rfl) size crhs cpower history (by rw [zero];exact phase)
    rhs0 power0 (Tx1Q_Carriers.accumulator out) (Tx1Q_Carriers.pending after) native
  exact rhs.trans JHk_RhsFacts.retained
#print axioms source
end AspisR1.JHk_CurrentRhsFormula
end
