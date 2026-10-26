import RPz7_F3L_PreparedPort
import RPz7_PFin_Gates
import RPz7_F3L_ModelRead
import RPz7_PSem_TypedPrefix
import RPz7_F3L_OpeningFields
import RPz7_F3K_OpeningQuery
import RPz7_F3K_OpeningFromSource
import RPz7_F3K_OpeningSuffix
import RPz7_F3J_NativeInput
import RPz7_F3J_First27
import RPz7_PAln_JoinedRun
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PFin_Prepared
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open OraclePortStoredDecisionDraftC4
open BorrowedClaimPrepared AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open AspisR1PublicPreparation.PreparedHashCode
open MultiproofConeCanonical OraclePortCompactDraft SourceGlobalOracleInitial SourceDigestLog
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem from_cut {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (H : Bytes → State)
    (backend : Tx1DigestLog.ByteOracleBackend (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) H)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf f.proof.val)) :
    ∃ (i : F3_Model.Input) (p : Parsed) (q : Fin 22 → Fin 262144)
      (source : RecordedBinaryExperimentBin.SourceInputs),
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      let tr := LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      OraclePortStoredParserC4.parseReached (bytesOf f.proof.val) tr=some p ∧
      Aligned p tr ∧ OraclePortSelectedDraft.queries tr=some q ∧
      OraclePortStoredDecisionDraftC4.input p q tr=some source ∧
      LiteralMatchingData.read (typedRows p q tr)=some source.data ∧
      LiteralQueryRead.decode source.queryBytes=some q ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) source.data q
        (SelectedChallengeMap.rhoOf source.rho) := by
  obtain ⟨i,pre,t0,t25,t26,t27,r25,r26,z0,z1,start,cs,init,v,c,
    hc,physical,stored,pub,tag,trace,order,valid,read25,call25,read26,call26,
    seed,logs,state,fields,q,queries,coords,parser,source,found,prepare⟩ :=
    F3L_PreparedPort.from_cut adapter ops reserved query geo B std
      accounts1 accounts2 saved f s cuts selected run header H backend w canonical
  have parserSource := parser
  rw [stored] at parserSource
  have gates := PFin_Gates.closed _ _ q _ source parserSource found queries
  exact ⟨i,_,q,source,physical,stored,parserSource,gates.1,queries,found,gates.2.1,gates.2.2,prepare⟩

#print axioms from_cut
end AspisR1.PFin_Prepared
end
