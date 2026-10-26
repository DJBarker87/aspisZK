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
namespace AspisR1.FIs_Literal
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
          FIs_Finish.Outcome finish tx2.v2 tx2.p2
            {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
            (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace
            parsed.semantic q tr i (OraclePortAcceptedContextC6.context parsed i view)))
theorem strengthen {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (stage : VTop_Stages.Ops) {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (authParsed : Parsed)
    (tx2 : Cons_Native.Witness)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (enriched : FIs_Native.Calls (AuS1_Install.base stage) finish reserved query geo D hash s.pub s.proof s.checkpoint tx2)
    (seed : AspisR1Stage2.Stage2Finish.FinishOps F) (installed : finish=FIn_Install.finishOps seed)
    (positions : stage.op22=ok 7527#usize ∧ stage.op21=ok 8007#usize ∧ stage.op20=ok 10055#usize)
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val)
    (old : Rc5_Literal.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2) :
    Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2 := by
  obtain ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,source,output,sourceNumeric,remaining⟩ := old
  refine ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,source,output,sourceNumeric,?_⟩
  rcases remaining with bad | good
  · exact Or.inl bad
  · right
    obtain ⟨acc,writer,len,next,savedEq,finishing⟩ := good
    refine ⟨acc,writer,len,next,savedEq,?_⟩
    let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program (Rc4_Model.typed raw).proof 0 33 (FS.emptyPrefix (Rc4_Model.typed raw).semantic.value))).2
    have parsedNative : OraclePortStoredParserC4.parseReached (bytesOf s.proof.val) tr=some parsed := by
      rw [sameProof,←stored]; exact parser
    have rounds := FIn_FromRead.rounds seed _ s.proof tx2 enriched.2.2
      positions.1 rfl rfl positions.2.1 parsed q _ _ parsedNative read
    have savedFields := Tx2N_Reader.saved_ten (AuS1_Install.base stage) reserved query D hash s.checkpoint s.proof s.pub
      saved tx2.p2 tx2.saved2 H (bytesOf f.proof.val) (bytesOf f.pub.val)
      (OraclePortAcceptedContextC6.context parsed _ view) _ _ q sameSaved savedEq enriched.1.1
    have size : tx2.saved2.weights.val.length=64 := by
      rw [savedFields.1.weights]
      simp only [List.length_map,List.length_ofFn]
    have length := (FIn_WeightLength.twelve reserved query geo D hash s.pub s.proof s.checkpoint tx2 enriched.2.1 size).1
    have dot := SAG_ShapeDot.value (AuS1_Install.base stage) finish reserved query geo D hash
      s.pub s.proof s.checkpoint tx2 enriched.1 _ enriched.2.2 positions.2.1 positions.2.2
      (by rw [installed]; rfl) length parsed q _ _ parsedNative read
    apply FIs_Finish.strengthen (old := finishing)
    · rw [installed]; exact rounds.1
    · rw [installed]; exact rounds.2
    · exact dot

#print axioms strengthen
end AspisR1.FIs_Literal
end
