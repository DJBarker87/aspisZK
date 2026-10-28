import NDO_JHl_WeightLoop
import NDO_JHl_InitialSum
import NDO_JHl_FlushSum
import NDO_JHk_CurrentQuery
import NDO_JHk_PowerInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_CurrentWeights
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open JHl_SumField (value)
attribute [local irreducible] JGp_Seeds.base JGp_Seeds.query JGp_Seeds.geometry
  JFx_NativeBytes.proof JFx_NativeBytes.publicInput

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (queries : p.queries=JFq_Queries.value)
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) (flush : installed.op17 after out.weights.deref=ok flushed) :
    ∀ j : Fin 64, ∃ q,flushed.val[j.val]?=some q ∧
      CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 j.val ∧
      Port3_FlushInstall.Canonical (Tx1Q_Carriers.k q) := by
  obtain ⟨alpha,rho,powers,geometry⟩ := JHk_PowerInputs.source p input scratch g prepare queries geo
  obtain ⟨size,zero,crhs,cpower,history,phase⟩ := JHa_Pending.source initial pending init pend
  have crho : Port3_FlushInstall.Canonical (Tx1Q_Carriers.prepared p).rho := by
    rw [rho]
    exact JFn_AccumulatorCanonical.rho
  have native := JHk_CurrentQuery.source p initial out scratch g pending after query
  rw [powers,geometry] at native
  have initialPower : CheckpointBytes5Output.ofK (Tx1Q_Carriers.accumulator initial).power=
      JHk_RhsFacts.power (Tx1Q_Carriers.accumulator initial).next.val := by
    rw [(JGw_InitialFacts.source initial init).2.2.1,zero]
    rfl
  obtain ⟨sum,trace,progress,sums,weights⟩ := JHl_WeightLoop.source
    (Tx1Q_Carriers.prepared p) (Port3_PendingInstall.owned (Tx1Q_Carriers.accumulator initial).weights.deref)
    queries alpha rho crho 10 (Tx1Q_Carriers.accumulator initial) (Tx1Q_Carriers.pending pending) _
    (by rw [zero];rfl) size crhs cpower history (by rw [zero];exact phase)
    (by intro j;rw [JHl_InitialSum.source initial init j,zero];rfl) initialPower
    (Tx1Q_Carriers.accumulator out) (Tx1Q_Carriers.pending after) native
  rw [JGw_InstalledSlots.flush] at flush
  have nativeFlush := Tx1Q_Install.flush_success after out.weights.deref flushed flush
  have oldEq : Tx1Q_Carriers.slice Tx1Q_Carriers.k out.weights.deref=
      (Tx1Q_Carriers.accumulator initial).weights.deref := by
    change (Tx1Q_Carriers.accumulator out).weights.deref=_
    rw [weights]
  rw [oldEq] at nativeFlush
  intro j
  obtain ⟨q,hget,meaning,canonical⟩ := JHl_FlushSum.source
    (Tx1Q_Carriers.accumulator initial).weights.deref (Tx1Q_Carriers.pending after)
    (Tx1Q_Carriers.slice Tx1Q_Carriers.k flushed) sum size progress.2.1 trace nativeFlush j
  change (flushed.val.map Tx1Q_Carriers.k)[j.val]?=some q at hget
  rw [List.getElem?_map] at hget
  cases hc : flushed.val[j.val]? with
  | none => simp only [hc,Option.map_none] at hget;cases hget
  | some x =>
    simp only [hc,Option.map_some,Option.some.injEq] at hget
    subst q
    exact ⟨x,rfl,meaning.trans (sums j),canonical⟩
#print axioms source
end AspisR1.JHl_CurrentWeights
end
