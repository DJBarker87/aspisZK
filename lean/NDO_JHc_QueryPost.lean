import NDO_JHc_InstalledQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_QueryPost
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open S7Kani3CallerTrace (PushTrace Sum)
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
      installed.op17 after out.weights.deref=ok flushed ∧
      out.next.val=10 ∧ flushed.val.length=64 ∧ p.variant=.S2 ∧
      Port4C_QueryArithmetic.CanonE (Tx1Q_Carriers.accumulator out).rhs ∧
      Port3_FlushInstall.Canonical (Tx1Q_Carriers.accumulator out).power := by
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
  have afterSize : after.raw.val.length=64 := progress.2.1
  have outSize : out.weights.val.length=64 := by rw [weights];exact size
  obtain ⟨flushed,hflush⟩ := JHc_InstalledQuery.flushNative after out.weights.deref outSize progress.2.1
  refine ⟨Tx1Q_Carriers.unAccumulator out,Tx1Q_Carriers.unPending after,
    Tx1Q_Carriers.slice Tx1Q_Carriers.unK flushed,?_,?_,?_,?_,rho.2.1,?_,?_⟩
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
  · exact next
  · change (flushed.val.map Tx1Q_Carriers.unK).length=64
    rw [List.length_map]
    exact (Port3_FlushInstall.accepted_contents after out.weights.deref flushed
      (by change out.weights.val.length≤after.raw.val.length;rw [outSize,afterSize]) hflush).2.trans outSize
  · rw [Tx1Q_Carriers.accumulator_roundtrip]
    exact cr
  · rw [Tx1Q_Carriers.accumulator_roundtrip]
    exact cp
#print axioms source
end AspisR1.JHc_QueryPost
end
