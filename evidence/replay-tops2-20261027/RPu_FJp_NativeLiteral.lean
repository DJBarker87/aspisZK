import RPz7_FIs_Literal
import RPu_FJp_NativeJoin
import RPu_FJp_Native
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_NativeLiteral
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
          FJp_Finish.Outcome finish tx2.v2 tx2.p2
            {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
            (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace
            parsed.semantic q tr i (OraclePortAcceptedContextC6.context parsed i view)))
theorem strengthen {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (saved : alloc.vec.Vec U8) (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (run : Tx1Q_Execution.Run
      (Tx1Q_Execution.actual (Op5T_Concrete.current (FIp_Install.configuration err seed r).currentBase)
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) std)
      (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
      (FIp_Install.configuration err seed r).geometry
      (SdkD_PairBatches.current (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase
        (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (authParsed : Parsed) (t : Cons_Native.Witness)
    (enriched : FJp_Native.Calls (AuS1_Install.base (FIp_Install.configuration err seed r).stageBase)
      (FIp_Install.configuration err seed r).finish (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (Tx1Q_Install.digest (SdkD_PairBatches.current
        (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase
        (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) std)) () s.pub s.proof s.checkpoint t)
    (sourceParsed : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some authParsed)
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val)
    (size : f.proof.val.length=57607)
    (authentication : ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
      (rho : OraclePortCheckpointAbiC5.K) (q : Fin 22 → Fin 262144),
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
      AuS1_Finish.Collision H trace authParsed q ∨
      ∃ recovered : Nat → Option Bytes,∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload authParsed 2 pos))
    (old : FIs_Literal.Outcome (FIp_Install.configuration err seed r).adapter
      (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
      B std saved f s run H trace authParsed t) :
    Outcome (FIp_Install.configuration err seed r).adapter
      (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
      B std saved f s run H trace authParsed t := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,remaining⟩ := old
  have parsed0 : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some parsed := by
    rw [←stored]
    exact (OraclePortStoredParserC4.parsed _ _ _ parser).1
  have equal : parsed=authParsed := Option.some.inj (parsed0.symm.trans sourceParsed)
  subst authParsed
  refine ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,?_⟩
  rcases remaining with hit | good
  · exact Or.inl hit
  · right
    obtain ⟨acc,writer,len,next,savedEq,finishing⟩ := good
    refine ⟨acc,writer,len,next,savedEq,?_⟩
    have auth := authentication _ _ q prepare
    exact FJp_NativeJoin.value err seed r (Op5T_Concrete.current c.currentBase)
      (F3M_CircleSource.install B) std _ () (AspisS6CurrentVerifierCarrier.toPublic f.semantic)
      f.pub f.proof f.split saved run s.checkpoint s.proof s.pub t enriched.1.2.1 enriched.2
      sameSaved sameProof size out parsed view q _ _ output sourceNumeric prepare read queries
      (OraclePortCompactDraft.parse_header _ _ parsed0).2 H trace _ auth finishing
#print axioms strengthen
end AspisR1.FJp_NativeLiteral
end
