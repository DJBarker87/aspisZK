import RPx_FJt_NativeAttach
/- New-prefix accepted-only consumer; source of origin: lean/SAP_SourceConsumer.lean. -/
import RPz7_SAP_Attach
import RPz7_SAF_C_SAP_FinishParsed
import SAP_InputQuery
import RPz7_T2R_Ten
import RPz7_Cons_Native
import RPz7_SAP_Discovery
import RPz7_F3P_PreparedSource
import RPz7_SAP_Immutable
import RPz7_SAP_SameDigest
import RPz7_SAP_Rebind
import RPz7_PAln_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_SourceConsumer
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
    (canonical : scan (bytesOf f.proof.val))
    (trace : List (Bytes × State)) (authParsed : Parsed)
    (sourceParsed : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some authParsed)
    (sameProof : bytesOf f.proof.val=bytesOf s.proof.val)
    (tx2 : Cons_Native.Witness)
    (ten : T2R_Ten.Outcome run H trace authParsed)
    (finishOld : SAF_C_T2R_Finish.Outcome finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace) :
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
        FIr_Remaining2.Endpoint i.decoded (typedRows parsed q tr) i.data ∧
        (∀ (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
          (geometry : Port5Q1_GeometryCanonical.SessionAPrimitives geo)
          (domain : Port5Q1_Domain.SessionADomain geo)
          (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
          (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned),
          AuS1_Finish.Collision H trace authParsed q ∨
          (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
            {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})=
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
              (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
          Port3_CheckpointInstall.writer (Tx1Q_Install.digest
            (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install (FIq_Install.boundaries seed)) std))
            (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator
              {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ()=ok saved ∧
          run.flushed.val.length=64 ∧ run.out.next.val=10)) ∧
        ∀ c : OraclePortCheckpointResumeC5.Context,
          SAF_C_SAP_FinishConsumer.Outcome finish tx2.v2 tx2.p2
            {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
            (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace
            parsed.semantic q tr i c := by
  obtain ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,out,same,equal,endpoint⟩ :=
    FJt_NativeAttach.from_cut adapter ops reserved query geo stage finish seed std accounts1 accounts2 saved f s
      cuts selected run header H native1 native2 hashv extraction sha256 p1 syscall w canonical
  have parsedSource := OraclePortStoredParserC4.parsed model.stored _ parsed parser
  have base : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some parsed := by
    rw [←stored]; exact parsedSource.1
  have sameParsed : parsed=authParsed := Option.some.inj (base.symm.trans sourceParsed)
  subst authParsed
  have wire : parsed.wire=bytesOf s.proof.val :=
    (OraclePortCompactDraft.parse_header _ _ base).2.trans sameProof
  refine ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,
    out,same,equal,endpoint,?_,?_⟩
  · intro ports geometry domain multiply one inverse
    exact ten ports q _ i.data (SelectedChallengeMap.rhoOf i.rho) prepare read
      geometry domain multiply one inverse
  · intro c
    exact SAF_C_SAP_FinishParsed.consume finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p parsed trace q _ i c finishOld
      wire found queries read (SAP_InputQuery.decoded _ _ _ _ found queries) prepare

#print axioms from_cut
end AspisR1.FJt_SourceConsumer
end
