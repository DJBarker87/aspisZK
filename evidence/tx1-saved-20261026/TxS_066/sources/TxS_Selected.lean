import F3Q_ConsPrepared
import F3Q_BodyOnRun
import F3N_WriterOnRun
import TxS_RawTen
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Selected
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open S2W_NativeConsolidation MultiproofConeCanonical
theorem same_run {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B0 : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B0) std)
      reserved query geo (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State)
    (backend : AspisR1PublicPreparation.Tx1DigestLog.ByteOracleBackend
      (retainedDigest (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)) H)
    (w : CanonicalCutEnrichedTranscript.Words)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B0) std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives geo) (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest
      (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std))) () H)
    (authParsed : OraclePortCompactDraft.Parsed) (parsed : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some authParsed)
    (trace : List (Bytes × State)) (ten : TxS_RawTen.Outcome run H trace authParsed) :
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (input : RecordedBinaryExperimentBin.SourceInputs) (out : AspisR1PublicPreparation.verifier.Prepared)
      (v : LiteralOpeningView.View),
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      currentPrepared out=run.p ∧
      F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
        (OraclePortAcceptedContextC6.context p input v) input.data (SelectedChallengeMap.rhoOf input.rho) q ∧
      (AuS1_Finish.Collision H trace p q ∨
        (saved=Tx2N_Reader.writer H i.stored i.physical.bytes
          (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p input v)
            input.data (SelectedChallengeMap.rhoOf input.rho) q)
          (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model input.data
            (SelectedChallengeMap.rhoOf input.rho) q)).accumulator ∧
         ∀ hp hu, CheckpointBytesDecodeC5.sourceBody (F3K_CheckpointPreparedFields.writerPrepared out)
           (CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator
             {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) hp hu=
           OraclePortCheckpointAbiC5.body
             (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p input v)
               input.data (SelectedChallengeMap.rhoOf input.rho) q)
             (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model input.data
               (SelectedChallengeMap.rhoOf input.rho) q)).accumulator
             (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu))) := by
  obtain ⟨i,p,q,input,out,v,physical,stored,parser,queries,found,prepare,output,read,prepared⟩ :=
    F3Q_ConsPrepared.from_cut a ops stage finish reserved query geo B0 std accounts1 accounts2 saved
      f s cuts selected run H backend w
  have sourceParser : OraclePortStoredParserC4.parseReached (bytesOf f.proof.val)
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p := by
    rw [← stored];exact parser
  have sourceBase := (OraclePortStoredParserC4.parsed _ _ _ sourceParser).1
  have sameParsed : p=authParsed := Option.some.inj (sourceBase.symm.trans parsed)
  subst authParsed
  have typed := TxS_RawTen.to_typed run H trace p ten
  have matching := (OraclePortStoredDecisionDraftC4.input_fields p q _ input found).2
  rcases typed ports q _ input.data (SelectedChallengeMap.rhoOf input.rho) prepare matching
      canonical domain multiply one inverse with collision | checked
  · exact ⟨i,p,q,input,out,v,physical,stored,output,prepared,Or.inl collision⟩
  · obtain ⟨native,encoded⟩ := F3N_WriterOnRun.saved _ reserved query geo _ () _ f.pub f.proof f.split saved
      run owner ports H oracle out output
    have body := F3Q_BodyOnRun.body _ reserved query geo _ () _ f.pub f.proof f.split saved
      run owner ports out output
    rw [prepared,checked.1] at encoded body
    exact ⟨i,p,q,input,out,v,physical,stored,output,prepared,
      Or.inr ⟨by rw [stored,physical];exact encoded,body⟩⟩

#print axioms same_run
end AspisR1.TxS_Selected
end
