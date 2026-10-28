import NDO_JHa_QueryLoop
import NDO_JHa_Pending
import NDO_JHa_CurrentFields
import NDO_JHa_CurrentRho
import NDO_JGw_SameGeometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_InstalledQuery
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open S7Kani3CallerTrace (PushTrace Sum)

theorem flushNative (b : AspisR1Stage2.verifier.BatchedWeights)
    (old : Slice AspisR1Stage2.aspis_core.field.QM31)
    (size : old.val.length=64) (length : b.raw.val.length=64) :
    ∃ out, Port3_FlushInstall.flush b old=ok out := by
  have bound : old.val.length≤b.raw.val.length := by omega
  exact ⟨_,Port3_FlushInstall.flush_exact b old bound⟩
#print axioms flushNative

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (queries : p.queries=JFq_Queries.value)
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g)) :
    ∃ out after flushed,
      installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after)) ∧
      installed.op17 after out.weights.deref=ok flushed := by
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have rho := JHa_CurrentRho.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have powers := JHa_Powers.source p input scratch prepare
  have geometry := JGw_SameGeometry.source p g queries geo
  obtain ⟨size,zero,crhs,cpower,history,phase⟩ := JHa_Pending.source initial pending init pend
  have crho : Port3_FlushInstall.Canonical (Tx1Q_Carriers.prepared p).rho := by
    change Port3_FlushInstall.Canonical (Tx1Q_Carriers.k p.rho)
    rw [rho.1]
    exact JFn_AccumulatorCanonical.rho
  obtain ⟨out,after,run,weights,next,cr,cp,sum,trace,progress⟩ := JHa_QueryLoop.suffix
    (Tx1Q_Carriers.prepared p) (Port3_PendingInstall.owned (Tx1Q_Carriers.accumulator initial).weights.deref)
    queries fields.2.2 crho 10 (Tx1Q_Carriers.accumulator initial) (Tx1Q_Carriers.pending pending)
    _ (by rw [zero];rfl) size crhs cpower history (by rw [zero];exact phase)
  have nativeQuery : Port3_NativeQueryBody.verifier.candidate.query_loop JHa_QueryLoop.ops
      JFx_NativeBytes.proof (Tx1Q_Carriers.prepared p) (Tx1Q_Carriers.accumulator initial)
      JFr_TX2_Powers.value none (JGp_Geometry.value () JGp_Seeds.geometry) (Tx1Q_Carriers.pending pending) 10#usize=
      ok (.Ok (out,after)) := run
  have outSize : out.weights.val.length=64 := by rw [weights];exact size
  obtain ⟨flushed,hflush⟩ := flushNative after out.weights.deref outSize progress.2.1
  refine ⟨Tx1Q_Carriers.unAccumulator out,Tx1Q_Carriers.unPending after,
    Tx1Q_Carriers.slice Tx1Q_Carriers.unK flushed,?_,?_⟩
  · change Tx1Q_Install.result (fun x => (Tx1Q_Carriers.unAccumulator x.1,Tx1Q_Carriers.unPending x.2))
      (Port3_NativeQueryBody.verifier.candidate.query_loop JHa_QueryLoop.ops JFx_NativeBytes.proof
        (Tx1Q_Carriers.prepared p) (Tx1Q_Carriers.accumulator initial)
        (Tx1Q_Carriers.arr Tx1Q_Carriers.e scratch) none (Tx1Q_Carriers.geometry g)
        (Tx1Q_Carriers.pending pending) 10#usize)=_
    rw [powers.2,geometry,nativeQuery]
    rfl
  · rw [JGw_InstalledSlots.flush]
    unfold Tx1Q_Install.flush
    rw [Tx1Q_Carriers.pending_roundtrip]
    have oldEq : Tx1Q_Carriers.slice Tx1Q_Carriers.k
        (Tx1Q_Carriers.unAccumulator out).weights.deref=out.weights.deref := by
      with_unfolding_all exact (congrArg
        (fun a : AspisR1Stage2.verifier.Accumulator => a.weights.deref)
        (Tx1Q_Carriers.accumulator_roundtrip out))
    rw [oldEq,hflush,bind_tc_ok]
#print axioms source
/-- Actual prepared TX1 query and flush on one shared retained-byte witness.
This does not assert batch, writer success, saved-byte identity or accepted1. -/
theorem inhabited :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
      (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      installed.op20 .S2=ok (.Ok initial) ∧ installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧
      installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after)) ∧
      installed.op17 after out.weights.deref=ok flushed := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,init,pend,geo,_meaning,_entry⟩ := JGr_Geometry.inhabited
  obtain ⟨out,after,flushed,query,flush⟩ :=
    JHc_InstalledQuery.source p _ scratch initial pending g prepare queries init pend geo
  exact ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,query,flush⟩
#print axioms inhabited
end AspisR1.JHc_InstalledQuery
end
