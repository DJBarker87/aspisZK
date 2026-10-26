import F3N_ConsDictionary
import F3N_SourceInput
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ConsSource
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation MultiproofConeCanonical

theorem from_cut {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current a ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State)
    (backend : AspisR1PublicPreparation.Tx1DigestLog.ByteOracleBackend
      (retainedDigest (SdkD_PairBatches.current a ops stage finish reserved query geo B std)) H)
    (w : CanonicalCutEnrichedTranscript.Words) :
    ∃ i : F3_Model.Input,F3N_SourceInput.Facts f run.p H i := by
  have sourceCuts : SourceCuts (ClaimsUnrolledSdk.sdkOps (F3N_ConsDictionary.adapter a stage finish reserved query geo)
      (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std)
      accounts1 accounts2 saved f s := by
    rw [← F3N_ConsDictionary.dictionary]
    exact cuts
  have uniCuts : SourceCuts (ClaimsUnrolledSdk.sdkOps (F3N_ConsDictionary.adapter a stage finish reserved query geo)
      (Uni_Install.current ops reserved query geo) B std) accounts1 accounts2 saved f s := by
    simpa only [AuS1_Install.dictionary,F3N_ConsDictionary.adapter] using cuts
  have header := (Op3I_Cuts.same_cut_header (F3N_ConsDictionary.adapter a stage finish reserved query geo)
    (Op5T_Concrete.current (Uni_Install.base ops reserved query geo)) B std
    accounts1 accounts2 saved f s uniCuts).2.2.1
  have canonical := (Uni_Cuts.scan (F3N_ConsDictionary.adapter a stage finish reserved query geo)
    ops reserved query geo B std accounts1 accounts2 saved f s uniCuts).2.2
  have result := F3N_SourceInput.from_cut (F3N_ConsDictionary.adapter a stage finish reserved query geo)
    (Op5T_Concrete.current ops) reserved query geo B std accounts1 accounts2 saved f s sourceCuts selected
    run header H backend w canonical
  exact result

#print axioms from_cut
end AspisR1.F3N_ConsSource
end
