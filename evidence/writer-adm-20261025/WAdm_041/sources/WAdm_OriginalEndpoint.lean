import WAdm_Endpoint
import WAdm_Inventory
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_OriginalEndpoint
open Tx1Q_Carriers S2W_NativeConsolidation

theorem reached {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (e1 : S2W_D189Entry.Entry) (accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      e1.first accounts2 saved f s)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual ops reserved query geo B std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std) reserved query geo
      (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
      reserved = true ∧ f.split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
      (∀ x ∈ (slice k run.flushed).val, Port3_FlushInstall.Canonical x) ∧
      WAdm_Domain.Admitted (prepared run.p)
        (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ∧
      WAdm_Carrier.WideInputs (prepared run.p)
        (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) ∧
      WAdm_SourceWriter.writer
        (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std))
        (prepared run.p) (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
        f.proof f.pub () = ok saved ∧ Tx1Q_Endpoint.WhenBound run := by
  have proofLength : f.proof.val.length = 57607 := by
    simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using cuts.proofLength
  obtain ⟨run,r,sp,n,w,can,writer,bound⟩ := Tx1Q_Endpoint.reached adapterOps ops reserved query geo B std
    e1.first accounts2 saved f s cuts proofLength
  have publicLength := (WAdm_Public.reached adapterOps (Tx1Q_SameCut.dictionary ops reserved query geo)
    B std e1 accounts2 saved f s cuts).2
  have domain := WAdm_Domain.on_run _ _ _ _ _ _ _ _ _ _ _ run owner ports proofLength publicLength
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run _ _ _ _ _ _ _ _ _ _ _ run owner ports
  have nativeContent : WAdm_SourceWriter.writer
      (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std))
      (prepared run.p) (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
      f.proof f.pub () = ok saved := by
    rw [WAdm_SourceWriter.writer_eq _ _ _ _ _ _ fields size canonical n]
    exact writer
  exact ⟨run,r,sp,n,w,can,domain,WAdm_Carrier.wide _ _ _ _ domain,nativeContent,bound⟩

#print axioms reached
end AspisR1.WAdm_OriginalEndpoint
end
