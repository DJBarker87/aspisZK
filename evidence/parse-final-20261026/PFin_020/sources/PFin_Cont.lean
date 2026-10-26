import PFin_Ten
import PFin_Finish
import PFin_Attach
import PFin_SelectedResult
import T2R_ContSource
import T2R_Finish
import Cons_Native
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_Cont
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

def Outcome {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prior : Program Bytes State Unit) (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness) : Prop :=
        ∀ (queryLeaves : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
          (geoLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps)
          (domain : Port5Q1_Domain.SessionADomain geoOps)
          (multiply : geoOps.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
          (one : geoOps.op7 = ok 1#u32) (inverse : geoOps.op11 = Port4C_InverseExecution.inverse_owned),
        ∃ authParsed frame,
          OraclePortCompactDraft.parse (bytesOf f.proof.val) = some authParsed ∧
          FS2.Duplex.Read ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
            (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) frame ∧
          BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot authParsed 2) ∧
          ∃ (modelInput : F3_Model.Input) (q : Fin 22 → Fin 262144)
            (i : RecordedBinaryExperimentBin.SourceInputs),
            modelInput.physical.bytes = bytesOf f.pub.val ∧ modelInput.stored = bytesOf f.proof.val ∧
            let tr := LiteralTranscript.erasePrefix (eval H
              (F3J_SamplerRun.program modelInput.proof 0 33 (FS.emptyPrefix modelInput.semantic.value))).2
            OraclePortStoredParserC4.parseReached (bytesOf f.proof.val) tr = some authParsed ∧
            OraclePortCompactDraft.Aligned authParsed tr ∧
            OraclePortSelectedDraft.queries tr = some q ∧
            OraclePortStoredDecisionDraftC4.input authParsed q tr = some i ∧
            LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows authParsed q tr) = some i.data ∧
            LiteralQueryRead.decode i.queryBytes = some q ∧
            Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p)
              i.data q (SelectedChallengeMap.rhoOf i.rho) ∧
            PFin_Ten.Outcome run H ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) authParsed q i.data (SelectedChallengeMap.rhoOf i.rho) ∧
            PFin_Finish.Outcome finishOps tx2.v2 tx2.p2 {tx2.returned2 with weights := tx2.back2 tx2.flushed2}
              s.proof saved H (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed
              ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) authParsed.semantic q tr i

theorem from_cut {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prior : Program Bytes State Unit) (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (cuts : SourceCuts (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement = ok f.semantic)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val) = true)
    (canonical : OraclePortCompactDraft.scan (bytesOf f.proof.val))
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd) native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (sameProof : bytesOf s.proof.val = bytesOf f.proof.val)
    (old : T2R_ContSource.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) :
    Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  let words := CanonicalCutEnrichedTranscript.wordsFromMaps (fun _=>none) (fun _=>none) (fun _=>none)
  obtain ⟨modelInput,p,q,i,physical,stored,reached,aligned,queries,found,read,decoded,prepare⟩ :=
    PFin_Attach.from_cut adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
      accounts1 accounts2 saved f s cuts selected run header H native1 native2 hashv extraction sha256 p1 syscall words canonical
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨authParsed,frame,parser,frameRead,target,ten,finish⟩ := old queryLeaves geoLeaves domain multiply one inverse
  have parser' := (OraclePortStoredParserC4.parsed _ _ _ reached).1
  have peq : p=authParsed := Option.some.inj (parser'.symm.trans parser)
  subst authParsed
  refine ⟨p,frame,parser,frameRead,target,modelInput,q,i,physical,stored,reached,aligned,queries,found,read,decoded,prepare,?_,?_⟩
  · exact PFin_Ten.consume run H _ p q i.data (SelectedChallengeMap.rhoOf i.rho) _ ten prepare read
  · apply PFin_Finish.consume finishOps tx2.v2 tx2.p2 _ s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p p _ q _ i finish
    · exact (OraclePortCompactDraft.parse_header _ _ parser).2.trans sameProof.symm
    · exact found
    · exact queries
    · exact prepare

#print axioms from_cut

end AspisR1.PFin_Cont
end
