import RPz8_F3V_PreparedModel
import RPz7_F3N_PreparedClaimSource
import RPz7_F3N_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SourceInput
open Aeneas Aeneas.Std Result AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open BorrowedClaimPrepared AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open AspisR1PublicPreparation.PreparedHashCode MultiproofConeCanonical OraclePortCompactDraft
open AspisR1PublicPreparation.SourceGlobalOracleInitial AspisR1PublicPreparation.SourceDigestLog
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

def Facts (physical proof : Slice U8) (prepared : AspisR1CurrentCaller.verifier.Prepared)
    (H : Bytes → State) (modelInput : F3_Model.Input) : Prop :=
  let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program modelInput.proof 0 33
    (FS.emptyPrefix modelInput.semantic.value))).2
  modelInput.physical.bytes=bytesOf physical.val ∧ modelInput.stored=bytesOf proof.val ∧
  ∃ (p : Parsed) (q : Fin 22 → Fin 262144) (i : RecordedBinaryExperimentBin.SourceInputs)
    (out : AspisR1PublicPreparation.verifier.Prepared) (v : LiteralOpeningView.View)
    (sourceView : AspisR1CurrentCaller.verifier.View)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified Unit)
    (scratch : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
    OraclePortStoredParserC4.parseReached modelInput.stored tr=some p ∧
    OraclePortSelectedDraft.queries tr=some q ∧
    OraclePortStoredDecisionDraftC4.input p q tr=some i ∧
    Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared prepared) i.data q (SelectedChallengeMap.rhoOf i.rho) ∧
    currentPrepared out=prepared ∧ F3L_PreparedModelSix.Fields out i q ∧
    (F3L_SourcePrepared.numeric out).roots=(fun j=>OraclePortBatchDraft.committedRoot p j.val) ∧
    LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr)=some v ∧
    (F3L_SourcePrepared.numeric out).semanticAlpha=(OraclePortAcceptedContextC6.context p i v).semanticAlpha ∧
    AspisR1ClaimPreparedBridge.OriginalPayloadClaimMeaning (retainedSem sem) (retainedView sourceView).y1
      (AspisR1ClaimPreparedBridge.toClaimE (retainedView sourceView).inactive)
      (AspisR1ClaimPreparedBridge.toClaimE out.gamma) (AspisR1ClaimPreparedBridge.toClaimE out.kappa)
      (AspisR1ClaimPreparedBridge.toClaimE out.claim)
      (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.toClaimE scratch) ∧
    i.data.c0=AspisR1CurrentPreparedClaim.Concrete.decode
      (AspisR1ClaimPreparedBridge.toClaimE (retainedView sourceView).inactive)

theorem from_run {F CoreError : Type} (config : DrvC_Installation.Configuration F CoreError)
    (ops : Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops CoreError) (B : FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (D : aspis_core.digest.Digest32 Unit)
    (statement : AdapterRw.Cuts.Statement) (semantic : Port1_Driver.Semantic)
    (physical proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (decodedCall : (DrvC_Installation.sdk config).op47 physical=ok (.Ok statement))
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D () (AspisS6CurrentVerifierCarrier.toPublic semantic) physical proof split saved)
    (header : OraclePortHeader.accepts (bytesOf proof.val)=true)
    (H : Bytes → State)
    (backend : Tx1DigestLog.ByteOracleBackend (retainedDigest D) H)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf proof.val)) :
    ∃ i : F3_Model.Input,Facts physical proof run.p H i := by
  obtain ⟨i,pre,t0,t25,t26,t27,r25,r26,z0,z1,start,cs,init,v,c,cstart,physical,stored,publicBytes,tag,
    trace,order,valid,read25,call25,read26,call26,seed,sampler,state,fields,q,queryRead,coordinates,
    parsed,sourceInput,found,port,out,output,six,roots,modelView,viewRead,alpha,
    point0,point1,block0,block1,points,circle0,circle1,challenge0,challenge1,
    sourceSem,sourceScratch,semanticSuccess,scratch,meaning,constant⟩ :=
    F3V_PreparedModel.from_run config ops reserved query geo B std D statement semantic physical proof split saved
      decodedCall selected run header H backend w canonical
  exact ⟨i,physical,stored,⟨bytesOf proof.val,pre.records.val.map (fun s=>bytesOf s.val)⟩,
    q,sourceInput,out,modelView,v,sourceSem,sourceScratch,parsed,queryRead,found,port,output,six,roots,
    viewRead,alpha,meaning,constant⟩

#print axioms from_run
end AspisR1.F3V_SourceInput
end
