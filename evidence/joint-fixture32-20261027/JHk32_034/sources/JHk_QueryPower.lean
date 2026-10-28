import JHk_QueryPowerLoop
import JHk_CurrentQuery
import JHk_KUnique
import JHk_Power10
import JHc_QueryPost
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_QueryPower
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open CheckpointBytes5Output (ofK)

/-- Numeric identity for the actual TX1 query result, independent of the
flush and writer. The final result is an operand, never an assumed identity. -/
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
    Tx1Q_Carriers.k out.power=JFq_Power.scalar := by
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have rho := JHa_CurrentRho.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have powers := JHa_Powers.source p input scratch prepare
  have geometry := JGw_SameGeometry.source p g queries geo
  obtain ⟨size,zero,crhs,cpower,history,phase⟩ := JHa_Pending.source initial pending init pend
  have crho : Port3_FlushInstall.Canonical (Tx1Q_Carriers.prepared p).rho := by
    change Port3_FlushInstall.Canonical (Tx1Q_Carriers.k p.rho)
    rw [rho.1]
    exact JFn_AccumulatorCanonical.rho
  have native := JHk_CurrentQuery.source p initial out scratch g pending after query
  rw [powers.2,geometry] at native
  have power := JHk_QueryPowerLoop.source (Tx1Q_Carriers.prepared p)
    (Port3_PendingInstall.owned (Tx1Q_Carriers.accumulator initial).weights.deref)
    queries fields.2.2 crho 10 (Tx1Q_Carriers.accumulator initial) (Tx1Q_Carriers.pending pending)
    _ (by rw [zero];rfl) size crhs cpower history (by rw [zero];exact phase)
    (Tx1Q_Carriers.accumulator out) (Tx1Q_Carriers.pending after) native
  have initialPower := (JGw_InitialFacts.source initial init).2.2.1
  rw [initialPower] at power
  have one : ofK Port2_Initial.oneK=1 := rfl
  change ofK (Tx1Q_Carriers.k out.power)=ofK Port2_Initial.oneK*ofK (Tx1Q_Carriers.k p.rho)^10 at power
  rw [one,one_mul,rho.1,JHk_Power10.retained] at power
  obtain ⟨out1,after1,flushed,run,flush,next,length,variant,rhs,canon⟩ :=
    JHc_QueryPost.source p input scratch initial pending g prepare queries init pend geo
  have same := congrArg Prod.fst (core.result.Result.Ok.inj (Result.ok.inj (run.symm.trans query)))
  rw [same] at canon
  exact JHk_KUnique.source _ _ canon JFn_AccumulatorCanonical.power power
#print axioms source
end AspisR1.JHk_QueryPower
end
