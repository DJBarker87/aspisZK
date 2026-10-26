import RPz7_SAP_LiteralFields
import RPz7_SAP_NumericTransport
import RPz7_SAF_FinishPrepared
import RPz7_SAF_LiteralOutcome
import RPz7_SAP_LiteralOutcome
import RPz7_SAP_SaveOnRun
import RPz7_SAP_Attach
import RPz7_SAP_FinishParsed
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
namespace AspisR1.SAF_PreparedOutcome
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
    ∃ (model : F3_Model.Input) (parsed : Parsed) (q : Fin 22 → Fin 262144)
      (i : RecordedBinaryExperimentBin.SourceInputs) (view : LiteralOpeningView.View),
      model.physical.bytes=bytesOf f.pub.val ∧ model.stored=bytesOf f.proof.val ∧
      let tr := LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program model.proof 0 33 (FS.emptyPrefix model.semantic.value))).2
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
            (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std))
            (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator
              {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ()=ok saved ∧
          run.flushed.val.length=64 ∧ run.out.next.val=10 ∧
          saved=Tx2N_Reader.writer H (bytesOf f.proof.val) (bytesOf f.pub.val)
            (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed i view)
              i.data (SelectedChallengeMap.rhoOf i.rho) q)
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
              (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
          SAF_FinishPrepared.Outcome finish tx2.v2 tx2.p2
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
    (base : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (reader : (Tx2N_Install.inner base reserved query).op18 D s.checkpoint s.proof s.pub .S2 hash =
      ok (.Ok (tx2.p2,tx2.saved2)))
    (same : bytesOf s.checkpoint.val = bytesOf saved.val)
    (old : SAF_LiteralOutcome.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2) :
    Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2 := by
  rcases old with ⟨model,parsed,q,i,view,physical,stored,parse,hq,hi,read,opening,fields,numeric,
    prepare,prep,sourcePrepared,current,numerics,rest⟩
  refine ⟨model,parsed,q,i,view,physical,stored,parse,hq,hi,read,opening,fields,numeric,
    prepare,prep,sourcePrepared,current,numerics,?_⟩
  intro ports geometry domain multiply one inverse
  rcases rest ports geometry domain multiply one inverse with collision | good
  · exact Or.inl collision
  · right
    rcases good with ⟨acc,writer,len,next,savedEq,finishing⟩
    have savedFields := Tx2N_Reader.saved_ten base reserved query D hash s.checkpoint s.proof s.pub
      saved tx2.p2 tx2.saved2 H (bytesOf f.proof.val) (bytesOf f.pub.val)
      (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho)
      q same savedEq reader
    have identities := SAF_PreparedPairing.identities tx2.p2 tx2.saved2 parsed i view q _ savedFields.1
    refine ⟨acc,writer,len,next,savedEq,?_⟩
    apply SAF_FinishPrepared.strengthen (old := finishing) (identities := identities)

#print axioms strengthen
end AspisR1.SAF_PreparedOutcome
end
