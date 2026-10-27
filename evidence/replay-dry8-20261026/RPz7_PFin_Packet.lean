import RPz7_PFin_Attach
import RPz7_PFin_Prepared
import RPz7_PFin_Digest
import RPz7_PAln_Oracle
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
namespace AspisR1.PFin_Packet
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open OraclePortStoredDecisionDraftC4
open BorrowedClaimPrepared AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open AspisR1PublicPreparation.PreparedHashCode
open MultiproofConeCanonical OraclePortCompactDraft SourceGlobalOracleInitial SourceDigestLog
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

/-- Derived parser packet, available before history/P2Prime or owner leaves.
Every field is an output on the source run, not a caller-supplied interface. -/
def Facts (publicBytes stored : Bytes) (prepared : AspisR1Stage2.verifier.Prepared) (H : Bytes → State) : Prop :=
    ∃ (i : F3_Model.Input) (p : Parsed) (q : Fin 22 → Fin 262144)
      (source : RecordedBinaryExperimentBin.SourceInputs),
      i.physical.bytes=publicBytes ∧ i.stored=stored ∧
      let tr := LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      OraclePortStoredParserC4.parseReached stored tr=some p ∧
      Aligned p tr ∧ OraclePortSelectedDraft.queries tr=some q ∧
      OraclePortStoredDecisionDraftC4.input p q tr=some source ∧
      LiteralMatchingData.read (typedRows p q tr)=some source.data ∧
      LiteralQueryRead.decode source.queryBytes=some q ∧
      Port5Q1_QueryPorts.SessionAPrepare prepared source.data q
        (SelectedChallengeMap.rhoOf source.rho)

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
    (canonical : scan (bytesOf f.proof.val)) : Facts (bytesOf f.pub.val) (bytesOf f.proof.val) (Tx1Q_Carriers.prepared run.p) H :=
  PFin_Attach.from_cut adapter ops reserved query geo stage finish B std accounts1 accounts2 saved f s
    cuts selected run header H native1 native2 hashv extraction sha256 p1 syscall w canonical

#print axioms from_cut
end AspisR1.PFin_Packet
end
