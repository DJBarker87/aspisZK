import RPz7_F3V_PreparedExact
import RPz7_F3R_PreparedSource
import RPz7_F3R_Admission
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3V_PreparedAdmitted
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open BorrowedClaimPrepared AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open AspisR1PublicPreparation.PreparedHashCode
open MultiproofConeCanonical OraclePortCompactDraft SourceGlobalOracleInitial SourceDigestLog
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem from_run {F CoreError : Type} (config : DrvC_Installation.Configuration F CoreError)
    (ops : Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops CoreError) (B : FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (D : aspis_core.digest.Digest32 Unit)
    (statement : AdapterRw.Cuts.Statement) (semantic : Port1_Driver.Semantic)
    (physical proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (decodedCall : (DrvC_Installation.sdk config).op47 physical=ok (.Ok statement))
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo D () (AspisS6CurrentVerifierCarrier.toPublic semantic) physical proof split saved)
    (header : OraclePortHeader.accepts (bytesOf proof.val)=true)
    (H : Bytes → State)
    (backend : Tx1DigestLog.ByteOracleBackend (retainedDigest D) H)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf proof.val)) (decoder : LiteralByteProtocol.Decoder) :
    ∃ (i : F3_Model.Input) (p : Parsed) (q : Fin 22 → Fin 262144)
      (input : RecordedBinaryExperimentBin.SourceInputs)
      (out : AspisR1PublicPreparation.verifier.Prepared) (v : LiteralOpeningView.View),
      i.physical.bytes=bytesOf physical.val ∧ i.stored=bytesOf proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored (LiteralTranscript.erasePrefix
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p ∧
      OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some q ∧
      OraclePortStoredDecisionDraftC4.input p q (LiteralTranscript.erasePrefix
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some input ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) input.data q
        (SelectedChallengeMap.rhoOf input.rho) ∧ currentPrepared out=run.p ∧
      LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q (LiteralTranscript.erasePrefix
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2))=some v ∧
      F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
        (OraclePortAcceptedContextC6.context p input v) input.data (SelectedChallengeMap.rhoOf input.rho) q ∧
      AspisR1PublicPreparation.PreparedHashCode.observe
        (AspisR1PublicPreparation.PreparedHashCode.run (SdkD_PrepareSource.code
          (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo)))
          (F3M_CircleSource.install B) std
          D
          (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () (Array.repeat 29#usize run.zero))).1=
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ∧
      OraclePortAdmission.Guard (LiteralTranscript.erasePrefix
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) := by
  obtain ⟨i,pre,t0,t25,t26,t27,r25,r26,z0,z1,start,cs,init,view,c,seed,physical,stored,pubBytes,tag,trace,order,
    valid,read25,circle25,read26,circle26,new,sampler,state,fields,q,queries,coordinates,parser,
    input,found,prepare,out,output,six,roots,v,read,alpha,point0,point1,block0,block1,points,
    circle0,circle1,parameter0,parameter1,sem,scratch,semantic,scratchEq,meaning,constant,prepared,preparationLog⟩ :=
    F3V_PreparedExact.from_run config ops reserved query geo B std D statement semantic physical proof split saved
      decodedCall selected run header H backend w canonical
  have admitted := F3R_Admission.guard decoder H i tag valid fields
  exact ⟨i,_,q,input,out,v,physical,stored,parser,queries,found,prepare,output,read,prepared,preparationLog,admitted⟩

#print axioms from_run
end AspisR1.F3V_PreparedAdmitted
end
