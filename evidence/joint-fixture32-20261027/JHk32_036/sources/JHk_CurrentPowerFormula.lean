import JHk_QueryPowerLoop
import JHk_CurrentQuery
import JHc_QueryPost
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_CurrentPowerFormula
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open CheckpointBytes5Output (ofK)
attribute [local irreducible] JGp_Seeds.base JGp_Seeds.query JGp_Seeds.geometry
  JFx_NativeBytes.proof JFx_NativeBytes.publicInput

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
    ofK (Tx1Q_Carriers.k out.power)=ofK (Tx1Q_Carriers.k initial.power)*
      ofK (Tx1Q_Carriers.k p.rho)^10 := by
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
  exact power
#print axioms source
end AspisR1.JHk_CurrentPowerFormula
end
