import RPz7_WAdm_SameCut
import RPz7_WAdm_ReferenceRun
import RPz7_WAdm_Public
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Endpoint
open Tx1Q_Carriers S2W_NativeConsolidation

/-- Endpoint on the SAME published source cuts. The bounded writer value
admission is an output. No native/reference equality, successful writer or
chosen preparation is an input. Existing owner contracts stay named. -/
theorem reached {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (e1 : S2W_D189Entry.Entry) (accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapterOps (WAdm_SameCut.dictionary ops reserved query geo) B std)
      e1.first accounts2 saved f s)
    (owner : WAdm_Domain.SessionAPrepare (WAdm_Execution.actual ops reserved query geo B std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    ∃ run : WAdm_Execution.Run (WAdm_Execution.actual ops reserved query geo B std) reserved query geo
      (WAdm_SameCut.callerDigest adapterOps ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
      reserved = true ∧ f.split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
      (∀ x ∈ (slice k run.flushed).val, Port3_FlushInstall.Canonical x) ∧
      WAdm_Domain.Admitted (prepared run.p)
        (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ∧
      WAdm_Carrier.WideInputs (prepared run.p)
        (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) ∧
      WAdm_SourceWriter.writer
        (Tx1Q_Install.digest (WAdm_SameCut.callerDigest adapterOps ops reserved query geo B std))
        (prepared run.p) (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
        f.proof f.pub () = ok saved ∧
      Tx1Q_Endpoint.WhenBound
        (WAdm_ReferenceRun.reference _ _ _ _ _ _ _ _ _ _ _ run owner ports) := by
  obtain ⟨run⟩ := WAdm_SameCut.reached adapterOps ops reserved query geo B std e1.first accounts2 saved f s cuts
  have control := WAdm_RunControl.fields _ _ _ _ _ _ _ _ _ _ _ run
  have proofLength : f.proof.val.length = 57607 := by
    simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using cuts.proofLength
  have publicLength := (WAdm_Public.reached adapterOps (WAdm_SameCut.dictionary ops reserved query geo)
    B std e1 accounts2 saved f s cuts).2
  have domain := WAdm_RunDomain.on_run _ _ _ _ _ _ _ _ _ _ _ run owner ports proofLength publicLength
  exact ⟨run,control.1,control.2.1,control.2.2.1,control.2.2.2.1,control.2.2.2.2,
    domain,WAdm_Carrier.wide _ _ _ _ domain,run.writer_call,
    Tx1Q_Endpoint.on_run _ _ _ _ _ _ _ _ _ _ _
      (WAdm_ReferenceRun.reference _ _ _ _ _ _ _ _ _ _ _ run owner ports) proofLength⟩

#print axioms reached
#print reached
end AspisR1.WAdm_Endpoint
end
