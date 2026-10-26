import PFin_Prepared
import PFin_Digest
import PAln_Oracle
import F3L_PreparedPort
import PFin_Gates
import F3L_ModelRead
import PSem_TypedPrefix
import F3L_OpeningFields
import F3K_OpeningQuery
import F3K_OpeningFromSource
import F3K_OpeningSuffix
import F3J_NativeInput
import F3J_First27
import PAln_JoinedRun
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PFin_Attach
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
    (stage : VTop_Stages.Ops) {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (H : Bytes → State)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
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
  let a := Tx2I_Install.install adapter
    (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stage) reserved query geo)) finish
  have inputCuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps a (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo)
        B std) accounts1 accounts2 saved f s := by
    simpa only [AuS1_Install.dictionary,Uni_Install.compose_tx1] using cuts
  have extracted : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps a (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo)
        B std) native1 native2 hashv := by
    simpa only [AuS1_Install.dictionary,Uni_Install.compose_tx1] using extraction
  have backend := PAln_Oracle.installed_backend a (Op5T_Concrete.current ops) reserved query geo
    B std native1 native2 hashv extracted sha256 H p1 syscall
  let r := PFin_Digest.transport (PFin_Digest.same adapter ops stage finish reserved query geo B std) run
  have result := PFin_Prepared.from_cut a (Op5T_Concrete.current ops) reserved query geo B std
    accounts1 accounts2 saved f s inputCuts selected r header H backend w canonical
  simpa only [r,PFin_Digest.prepared] using result

#print axioms from_cut
end AspisR1.PFin_Attach
end
