import FJp_NativeLiteral
import FJu_Finish
import FIr_GlobalOwners2
import FIs_Literal
import FJp_NativeJoin
import FJp_Native
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJu_NativeLiteral
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
          FJu_Finish.Outcome finish tx2.v2 tx2.p2
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
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (old : FJp_NativeLiteral.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2) :
    Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2 := by
  obtain ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,remaining⟩ := old
  refine ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,?_⟩
  rcases remaining with hit | good
  · exact Or.inl hit
  · right
    obtain ⟨acc,writer,len,next,savedEq,finishing⟩ := good
    refine ⟨acc,writer,len,next,savedEq,?_⟩
    apply FJu_Finish.strengthen (old := finishing)
    intro terminal selectedView claim polys opening claimRead polyRead
    have physicalParser := parser
    rw [stored] at physicalParser
    have sameRows : (⟨bytesOf s.proof.val,parsed.semantic⟩ : Parsed)=parsed := by
      have wire := sameProof.trans (OraclePortCompactDraft.parse_header _ _ (OraclePortStoredParserC4.parsed _ _ _ physicalParser).1).2.symm
      rw [wire]
    rw [sameRows] at opening
    have first := FIr_PhysicalInitial.on_run (Op5T_Concrete.current ops)
      reserved query geo (F3M_CircleSource.install B) std
      (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
      parsed q _ physicalParser selectedView claim polys opening claimRead polyRead
    have sameView := Option.some.inj (opened.symm.trans opening)
    subst selectedView
    have chain := FIr_PhysicalChain.on_run (Op5T_Concrete.current ops)
      reserved query geo (F3M_CircleSource.install B) std
      (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
      parsed q _ physicalParser view claim polys opening claimRead polyRead
      out output _ sourceNumeric
      (fun j=>FIr_TranscriptRange.view H (Rc4_Model.typed raw).proof (Rc4_Model.typed raw).semantic.value
        parsed q view opening (15+j.val))
    exact ⟨first,chain,terminal view claim polys (by rw [sameRows];exact opening) claimRead polyRead⟩

#print axioms strengthen
end AspisR1.FJu_NativeLiteral
end
