import RPz7_Uni_Install
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Uni_Cuts
open Tx1Q_Carriers Tx1Q_Endpoint
theorem tx1 {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps (Uni_Install.current ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (length : f.proof.val.length = 57607) :
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std) reserved query geo
      (Tx1Q_SameCut.callerDigest adapterOps (Op5T_Concrete.current ops) reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
      reserved = true ∧ f.split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
      (∀ x ∈ (Tx1Q_Carriers.slice k run.flushed).val, Port3_FlushInstall.Canonical x) ∧
      Port3_CheckpointInstall.writer
        (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest adapterOps (Op5T_Concrete.current ops) reserved query geo B std))
        (prepared run.p) (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
        f.proof f.pub () = ok saved ∧ WhenBound run := by
  apply Tx1Q_Endpoint.reached adapterOps (Op5T_Concrete.current ops) reserved query geo B std
    accounts1 accounts2 saved f s _ length
  simpa only [Uni_Install.compose_tx1] using cuts

theorem scan {C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps (Uni_Install.current ops reserved query geo) B std)
      accounts1 accounts2 saved f s) :
    (RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std).op4 f.proof =
      ok (.Ok ()) ∧ Op4P_Install.sourceBody f.proof = ok (.Ok ()) ∧
      OraclePortCompactDraft.scan (MultiproofConeCanonical.bytesOf f.proof.val) := by
  apply Op4P_Cuts.same_cut_scan adapterOps
    (Tx1Q_Execution.base (Op5T_Concrete.current ops) reserved query geo) B std accounts1 accounts2 saved f s
  simpa only [Uni_Install.compose_tx1,Tx1Q_SameCut.dictionary] using cuts

#print axioms tx1
#print axioms scan
end AspisR1.Uni_Cuts
end
