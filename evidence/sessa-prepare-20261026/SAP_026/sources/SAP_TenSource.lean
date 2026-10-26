import SAP_Discovery
import T2R_Ten
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_TenSource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
theorem from_cut {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) (F3M_CircleSource.install B) std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo (Tx1Q_SameCut.callerDigest adapter ops reserved query geo (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (H : Bytes → State)
    (backend : Tx1DigestLog.ByteOracleBackend (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo (F3M_CircleSource.install B) std)) H)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf f.proof.val))
    (trace : List (Bytes × State)) (authParsed : Parsed)
    (sourceParsed : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some authParsed)
    (ten : T2R_Ten.Outcome run H trace authParsed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (geoCanonical : Port5Q1_GeometryCanonical.SessionAPrimitives geo)
    (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned) :
    ∃ (model : F3_Model.Input) (q : Fin 22 → Fin 262144)
      (i : RecordedBinaryExperimentBin.SourceInputs) (view : LiteralOpeningView.View),
      model.physical.bytes=bytesOf f.pub.val ∧ model.stored=bytesOf f.proof.val ∧
      let tr := LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program model.proof 0 33 (FS.emptyPrefix model.semantic.value))).2
      OraclePortStoredParserC4.parseReached model.stored tr=some authParsed ∧
      OraclePortSelectedDraft.queries tr=some q ∧ input authParsed q tr=some i ∧
      LiteralMatchingData.read (typedRows authParsed q tr)=some i.data ∧
      LiteralOpeningView.read (typedRows authParsed q tr)=some view ∧
      ∃ sourcePrepared : AspisR1PublicPreparation.verifier.Prepared,
        currentPrepared sourcePrepared=run.p ∧
        F3L_SourcePrepared.numeric sourcePrepared=OraclePortCheckpointResumeC5.prepared
          (OraclePortAcceptedContextC6.context authParsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q ∧
        (AuS1_Finish.Collision H trace authParsed q ∨
          (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
              {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})=
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
              (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
           Port3_CheckpointInstall.writer (Tx1Q_Install.digest
              (Tx1Q_SameCut.callerDigest adapter ops reserved query geo (F3M_CircleSource.install B) std))
              (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator
                {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ()=ok saved ∧
           run.flushed.val.length=64 ∧ run.out.next.val=10)) := by
  obtain ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,out,same,equal⟩ :=
    SAP_Discovery.from_cut adapter ops reserved query geo B std accounts1 accounts2 saved f s cuts
      selected run header H backend w canonical
  have parsedSource := OraclePortStoredParserC4.parsed model.stored _ parsed parser
  have base : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some parsed := by
    rw [←stored];exact parsedSource.1
  have sameParsed : parsed=authParsed := Option.some.inj (base.symm.trans sourceParsed)
  subst parsed
  have checked := ten ports q _ i.data (SelectedChallengeMap.rhoOf i.rho) prepare read
    geoCanonical domain multiply one inverse
  exact ⟨model,q,i,view,physical,stored,parser,queries,found,read,opening,out,same,equal,checked⟩

#print axioms from_cut
end AspisR1.SAP_TenSource
end
