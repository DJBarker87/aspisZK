import FJt_NativeFinish
import FJt_SourceConsumer
import FIs_OnRun
import Rc5_Literal
import FIs_Finish
import FIs_Native
import FIn_FromRead
import FIn_WeightLength
import SAG_ShapeDot
import SAF_C_SAF_FinishPrepared
import SAF_C_SAF_PreparedOutcome

import Rc4_Model
import SAQ_Constructor
import SAQ_Decoder
import SAP_LiteralFields
import SAP_NumericTransport
import SAF_C_SAF_FinishPrepared
import SAP_SaveOnRun
import SAP_Attach
import SAP_FinishParsed
import SAP_InputQuery
import T2R_Ten
import Cons_Native
import SAP_Discovery
import F3P_PreparedSource
import SAP_Immutable
import SAP_SameDigest
import SAP_Rebind
import PAln_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_Literal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
def Outcome {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (stage : VTop_Stages.Ops) {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (authParsed : Parsed)
    (tx2 : Cons_Native.Witness) : Prop :=
    ∃ (rawModel : Rc4_Model.Input) (parsed : Parsed) (q : Fin 22 → Fin 262144)
      (metadata : TxS_Carriers.Metadata) (view : LiteralOpeningView.View),
      let model := Rc4_Model.typed rawModel
      let tr := LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program model.proof 0 33 (FS.emptyPrefix model.semantic.value))).2
      let i := TxS_Carriers.source metadata (typedRows parsed q tr)
      model.physical.bytes=bytesOf f.pub.val ∧ model.stored=bytesOf f.proof.val ∧
      OraclePortStoredParserC4.parseReached model.stored tr=some parsed ∧
      OraclePortSelectedDraft.queries tr=some q ∧ input parsed q tr=some i ∧
      LiteralMatchingData.read (typedRows parsed q tr)=some i.data ∧
      LiteralOpeningView.read (typedRows parsed q tr)=some view ∧
      SAP_LiteralFields.Fields run.p i q (OraclePortAcceptedContextC6.context parsed i view) ∧
      SAP_CurrentNumeric.numeric run.p=OraclePortCheckpointResumeC5.prepared
        (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) i.data q
        (SelectedChallengeMap.rhoOf i.rho) ∧
      Port5Q2_Prepared.PreparedFields (Tx1Q_Carriers.prepared run.p) ∧
      ∃ sourcePrepared : AspisR1PublicPreparation.verifier.Prepared,
        currentPrepared sourcePrepared=run.p ∧
        F3L_SourcePrepared.numeric sourcePrepared=OraclePortCheckpointResumeC5.prepared
          (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q ∧
        (AuS1_Finish.Collision H trace authParsed q ∨
          (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
            {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})=
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
              (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
          Port3_CheckpointInstall.writer (Tx1Q_Install.digest
            (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std))
            (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator
              {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ()=ok saved ∧
          run.flushed.val.length=64 ∧ run.out.next.val=10 ∧
          saved=Tx2N_Reader.writer H (bytesOf f.proof.val) (bytesOf f.pub.val)
            (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed i view)
              i.data (SelectedChallengeMap.rhoOf i.rho) q)
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
              (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
          FJt_NativeFinish.Outcome finish tx2.v2 tx2.p2
            {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
            (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace
            parsed.semantic q tr i (OraclePortAcceptedContextC6.context parsed i view)))
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
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (geometry : Port5Q1_GeometryCanonical.SessionAPrimitives geo)
    (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (enriched : FIs_Native.Calls (AuS1_Install.base stage) finish reserved query geo D hash s.pub s.proof s.checkpoint tx2)
    (finishSeed : AspisR1Stage2.Stage2Finish.FinishOps F) (installed : finish=FIn_Install.finishOps finishSeed)
    (positions : stage.op22=ok 7527#usize ∧ stage.op21=ok 8007#usize ∧ stage.op20=ok 10055#usize)
    (sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val) :
    Outcome adapter ops reserved query geo stage finish (FIq_Install.boundaries seed) std
      saved f s run H trace authParsed tx2 := by
  obtain ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,
    out,same,equal,endpoint,ten,finishOld⟩:=FJt_SourceConsumer.from_cut adapter ops reserved query geo stage finish seed std
      accounts1 accounts2 saved f s cuts selected run header H native1 native2 hashv extraction sha256 p1 syscall w canonical
      trace authParsed sourceParsed sameProof tx2 ten finishOld
  have current : SAP_CurrentNumeric.numeric run.p=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q := by
    rw [←same,SAP_NumericTransport.numeric]
    exact equal
  refine ⟨Rc4_Model.erase model,parsed,q,TxS_Carriers.eraseInput i,view,?_⟩
  dsimp only
  rw [Rc4_Model.typed_erase,TxS_Carriers.source_of_read _ i read]
  refine ⟨physical,stored,parser,queries,found,read,opening,SAP_LiteralFields.of_numeric run.p i q _ current,
    current,prepare,fields,out,same,equal,?_⟩
  rcases ten ports geometry domain multiply one inverse with collision | indexed
  · exact Or.inl collision
  · right
    have oracle:=F3N_SameOracle.current adapter ops stage finish reserved query geo
      (F3M_CircleSource.install (FIq_Install.boundaries seed)) std native1 native2 hashv extraction sha256 H p1 syscall
    have sourceSaved:=SAP_SaveOnRun.saved (Op5T_Concrete.current ops) reserved query geo (FIq_Install.boundaries seed) std
      _ () _ f.pub f.proof f.split saved run ports H oracle out same
    rw [equal,indexed.1] at sourceSaved
    refine ⟨indexed.1,indexed.2.1,indexed.2.2.1,indexed.2.2.2,sourceSaved,?_⟩
    have finishSaved:=SAF_C_SAP_FinishSaved.consume finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace parsed.semantic q _ i
      (OraclePortAcceptedContextC6.context parsed i view) (finishOld _) sourceSaved
    have finished:=SAF_C_SAF_FinishSaved.strengthen (old:=finishSaved) (success:=enriched.1.2.2.2.2.2.2.2.2.1)
    have savedFields:=Tx2N_Reader.saved_ten (AuS1_Install.base stage) reserved query D hash s.checkpoint s.proof s.pub
      saved tx2.p2 tx2.saved2 H (bytesOf f.proof.val) (bytesOf f.pub.val)
      (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho)
      q sameSaved sourceSaved enriched.1.1
    have identities:=SAF_PreparedPairing.identities tx2.p2 tx2.saved2 parsed i view q _ savedFields.1
    have prepared:=SAF_C_SAF_FinishPrepared.strengthen (old:=finished) (identities:=identities)
    have parsedNative:=parser
    rw [stored, sameProof] at parsedNative
    have size : tx2.saved2.weights.val.length=64 := by
      rw [savedFields.1.weights]
      simp only [List.length_map,List.length_ofFn]
    have onRun:=FIs_OnRun.strengthen (AuS1_Install.base stage) finish finishSeed reserved query geo D hash
      s.pub s.proof s.checkpoint saved tx2 enriched.1 enriched.2.1 _ enriched.2.2
      positions.1 rfl rfl positions.2.1 positions.2.2 installed size H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed parsed trace q _ i _ parsedNative read prepared
    have wire : (⟨bytesOf s.proof.val,parsed.semantic⟩ : Parsed)=parsed := by
      have h:=(OraclePortCompactDraft.parse_header _ _ (OraclePortStoredParserC4.parsed _ _ _ parsedNative).1).2
      cases parsed
      simp_all
    apply FJt_NativeFinish.strengthen (old:=onRun)
    rw [wire]
    exact endpoint
#print axioms from_cut
end AspisR1.FJt_Literal
end
