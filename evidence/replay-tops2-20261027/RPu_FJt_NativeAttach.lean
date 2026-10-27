import RPz7_SAP_Discovery
import RPu_FJt_NativeDiscovery
import RPu_FJt_CurrentCode
import RPz7_F3P_PreparedSource
import RPz7_SAP_Immutable
import RPz7_SAP_SameDigest
import RPz7_SAP_Rebind
import RPz7_PAln_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_NativeAttach
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
theorem from_cut {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (stage : VTop_Stages.Ops) {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (seed : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo (F3M_CircleSource.install (FIq_Install.boundaries seed)) std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install (FIq_Install.boundaries seed)) std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install (FIq_Install.boundaries seed)) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (H : Bytes → State)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo (F3M_CircleSource.install (FIq_Install.boundaries seed)) std)
      native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf f.proof.val)) :
    ∃ (model : F3_Model.Input) (parsed : Parsed) (q : Fin 22 → Fin 262144)
      (i : RecordedBinaryExperimentBin.SourceInputs) (view : LiteralOpeningView.View),
      model.physical.bytes=bytesOf f.pub.val ∧ model.stored=bytesOf f.proof.val ∧
      let tr := LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program model.proof 0 33 (FS.emptyPrefix model.semantic.value))).2
      OraclePortStoredParserC4.parseReached model.stored tr=some parsed ∧
      OraclePortSelectedDraft.queries tr=some q ∧ input parsed q tr=some i ∧
      LiteralMatchingData.read (typedRows parsed q tr)=some i.data ∧
      LiteralOpeningView.read (typedRows parsed q tr)=some view ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) i.data q
        (SelectedChallengeMap.rhoOf i.rho) ∧
      Port5Q2_Prepared.PreparedFields (Tx1Q_Carriers.prepared run.p) ∧
      ∃ sourcePrepared : AspisR1PublicPreparation.verifier.Prepared,
        currentPrepared sourcePrepared=run.p ∧
        F3L_SourcePrepared.numeric sourcePrepared=OraclePortCheckpointResumeC5.prepared
          (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q ∧
        FIr_Remaining2.Endpoint i.decoded (typedRows parsed q tr) i.data := by
  let config : DrvC_Installation.Configuration F CoreError :=
    ⟨adapter,ops,stage,finish,reserved,query,geo,F3M_CircleSource.install (FIq_Install.boundaries seed),std⟩
  have extracted : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk config) native1 native2 hashv := by
    rw [DrvC_Installation.aus1_dictionary]
    exact extraction
  have backend : Tx1DigestLog.ByteOracleBackend
      (retainedDigest (SdkD_PairBatches.current adapter ops stage finish reserved query geo
        (F3M_CircleSource.install (FIq_Install.boundaries seed)) std)) H := by
    intro q actual
    obtain ⟨hash,input,output,same,returned⟩:=actual
    cases hash
    subst q
    change (DrvC_Installation.sdk config).op43 () input=ok output at returned
    rw [extracted.digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
    exact (syscall.returningValue input output returned).trans (p1.realization _)
  have decoded : (DrvC_Installation.sdk config).op47 f.pub=ok (.Ok f.statement) := cuts.decode
  obtain ⟨model,parsed,q,i,out,view,physical,stored,parser,queries,found,prepare,same,opened,numeric,logs,guard,endpoint⟩:=
    FJt_NativeDiscovery.from_run config (Op5T_Concrete.current ops) reserved query geo seed std _
      f.statement f.semantic f.pub f.proof f.split saved decoded selected run header H backend w canonical
      (fun _ _=>none)
  exact ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,(input_fields _ _ _ i found).2,opened,
    prepare,SAP_Immutable.on_run (Op5T_Concrete.current ops) reserved query geo (FIq_Install.boundaries seed) std _ () _ f.pub f.proof f.split saved run,
    out,same,numeric,endpoint⟩

#print axioms from_cut
end AspisR1.FJt_NativeAttach
end
