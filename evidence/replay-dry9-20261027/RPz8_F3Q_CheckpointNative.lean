import RPz8_F3Q_BodyOnRun
import RPz8_F3Q_ConsPrepared
import RPz8_F3N_SameRunTen
import RPz7_F3N_WriterOnRun
import RPz8_F3N_SameSecond
import RPz8_F3N_ReaderNumeric
import RPz7_F3N_SameOracle
import RPz8_F3N_TenInput
import RPz8_F3N_ModelBody
import S2X_RuntimeRetention
import RPz8_F3N_AuthenticatedTen
import RPz8_F3N_SameRun
import RPz7_PAln_Oracle
import RPz7_RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_CheckpointNative
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation MultiproofConeCanonical

theorem accepted {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B0 : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B0) std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives geo) (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned) :
    ∃ f s log,
      SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
        accounts1 accounts2 saved f s ∧ RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
        (S2W_Observation.two (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
          id accounts1 data1 accounts2 data2 slot) []=ok (.Ok saved,log) ∧
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B0) std)
      reserved query geo (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ (rootView : Slice U8),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        f.proof {start:=7751#usize,«end»:=7783#usize}=ok rootView ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootView=ok (.Ok run.root) ∧
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (input : RecordedBinaryExperimentBin.SourceInputs) (out : AspisR1PublicPreparation.verifier.Prepared)
      (v : LiteralOpeningView.View) (tx2 : Cons_Native.Witness),
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored (LiteralTranscript.erasePrefix
        (AspisV8R19.MemoizedProgramLaw.eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p ∧
      OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix
        (AspisV8R19.MemoizedProgramLaw.eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some q ∧
      OraclePortStoredDecisionDraftC4.input p q (LiteralTranscript.erasePrefix
        (AspisV8R19.MemoizedProgramLaw.eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some input ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) input.data q
        (SelectedChallengeMap.rhoOf input.rho) ∧ currentPrepared out=run.p ∧
      F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
        (OraclePortAcceptedContextC6.context p input v) input.data (SelectedChallengeMap.rhoOf input.rho) q ∧
      Cons_Native.Calls (AuS1_Install.base stage) finish reserved query geo
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)) ()
        s.pub s.proof s.checkpoint tx2 ∧
      (WAdm_NativeInstall.install (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B0) std)).op16
        (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std) run.p
        {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} f.proof f.pub ()=ok saved ∧
      ∀ (prior : AspisV8R19.MemoizedProgramLaw.Program Bytes State Unit)
        (history : S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val))
        (sameProof : bytesOf s.proof.val=bytesOf f.proof.val),
        let trace := (AspisV8R19.MemoizedProgramLaw.eval H prior).1 ++
          AuS1_Recovery.log (Uni_Install.current ops reserved query geo) (F3M_CircleSource.install B0) std
            (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)
        AuS1_Finish.Collision H trace p q ∨
        (saved=Tx2N_Reader.writer H i.stored i.physical.bytes
          (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p input v)
            input.data (SelectedChallengeMap.rhoOf input.rho) q)
          (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model input.data
            (SelectedChallengeMap.rhoOf input.rho) q)).accumulator ∧
         CheckpointBytes4SavedFields.BodyMatches tx2.p2 tx2.saved2
          (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p input v)
            input.data (SelectedChallengeMap.rhoOf input.rho) q)
          (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model input.data
            (SelectedChallengeMap.rhoOf input.rho) q)).accumulator ∧
         CheckpointBytes5Output.accumulator tx2.saved2=
          (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model input.data
            (SelectedChallengeMap.rhoOf input.rho) q)).accumulator ∧
         ∀ hp hu, CheckpointBytesDecodeC5.sourceBody (F3K_CheckpointPreparedFields.writerPrepared out)
          (CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator
            {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) hp hu=
          OraclePortCheckpointAbiC5.body
            (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p input v)
              input.data (SelectedChallengeMap.rhoOf input.rho) q)
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model input.data
              (SelectedChallengeMap.rhoOf input.rho) q)).accumulator
            (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu)) := by
  let B := F3M_CircleSource.install B0
  obtain ⟨f,s,log,cuts,recorded,ran,run,view,oldInput,range,copy,facts,ten⟩ :=
    F3N_SameRunTen.accepted a ops stage finish reserved query geo B std native1 native2 hashv extraction
      id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2 sha256 H p1 syscall w
  have extracted : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps (F3N_ConsDictionary.adapter a stage finish reserved query geo)
        (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std)
      native1 native2 hashv := by rw [← F3N_ConsDictionary.dictionary];exact extraction
  have backend := PAln_Oracle.installed_backend (F3N_ConsDictionary.adapter a stage finish reserved query geo)
    (Op5T_Concrete.current ops) reserved query geo B std native1 native2 hashv extracted sha256 H p1 syscall
  obtain ⟨i,p,q,input,out,v,physical,stored,parser,queries,found,prepare,output,read,prepared⟩ :=
    F3Q_ConsPrepared.from_cut a ops stage finish reserved query geo B0 std accounts1 accounts2 saved
      f s cuts recorded.1 run H backend w
  have oracle := F3N_SameOracle.current a ops stage finish reserved query geo B std native1 native2 hashv
    extraction sha256 H p1 syscall
  obtain ⟨writer,encoded⟩ := F3N_WriterOnRun.saved _ reserved query geo _ () _ f.pub f.proof f.split saved
    run owner ports H oracle out output
  obtain ⟨tx2,calls,aux⟩ := F3N_SameSecond.from_cut a ops stage finish reserved query geo B std
    accounts1 accounts2 saved f s cuts
  refine ⟨f,s,log,cuts,recorded,ran,run,view,range,copy,i,p,q,input,out,v,tx2,physical,stored,parser,queries,found,prepare,output,prepared,calls,writer,?_⟩
  intro prior history sameProof
  have same := S2X.checkpoint_persistence _ _ history
  have parserSource : OraclePortStoredParserC4.parseReached (bytesOf f.proof.val) (LiteralTranscript.erasePrefix
      (AspisV8R19.MemoizedProgramLaw.eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p := by
    rw [← stored];exact parser
  have base := (OraclePortStoredParserC4.parsed _ _ _ parserSource).1
  obtain ⟨frame,frameRead,target,bound⟩ := ten prior same sameProof p base
  rcases F3N_TenInput.same_input run H _ p bound ports q _ input prepare parserSource found
    canonical domain multiply one inverse with collision | checked
  · exact Or.inl collision
  · have next : (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
        {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})).next=10 := by
      exact (Tx1Q_Control.fields _ reserved query geo _ () _ f.pub f.proof f.split saved run).2.2.1
    have reader := F3N_ReaderNumeric.saved_ten (AuS1_Install.base stage) reserved query _ ()
      s.checkpoint s.proof s.pub saved tx2.p2 tx2.saved2 H (bytesOf f.proof.val) (bytesOf f.pub.val)
      (F3L_SourcePrepared.numeric out) _ next same encoded calls.1
    rw [prepared,checked.1] at encoded reader
    refine Or.inr ⟨by rw [stored,physical];exact encoded,reader.1,reader.2.1,?_⟩
    intro hp hu
    have body := F3Q_BodyOnRun.body _ reserved query geo _ () _ f.pub f.proof f.split saved
      run owner ports out output hp hu
    rw [prepared,checked.1] at body
    exact body

#print axioms accepted
end AspisR1.F3Q_CheckpointNative
end
