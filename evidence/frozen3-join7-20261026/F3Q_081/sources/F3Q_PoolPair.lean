import F3Q_PairCheckpointLog
import PoolT_Write
import F3Q_PairBatches
import F3Q_CheckpointLogOnRun
import F3Q_CheckpointNative
import F3Q_FirstBatch
import F3Q_SecondBatch
import F3Q_BodyOnRun
import F3Q_ConsPrepared
import F3N_SameRunTen
import F3N_WriterOnRun
import F3N_SameSecond
import F3N_ReaderNumeric
import F3N_SameOracle
import F3N_TenInput
import F3N_ModelBody
import S2X_RuntimeRetention
import F3N_AuthenticatedTen
import F3N_SameRun
import PAln_Oracle
import RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_PoolPair
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation MultiproofConeCanonical

theorem accepted {F C A : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B0 : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std) native1 native2 hashv)
    (copyFn : S2Trust.Heap (Nat → S2W_D189Entry.Record) → Nat → S2W_TrustedStd.Payload → S2W_TrustedStd.Outcome (Nat → S2W_D189Entry.Record))
    (copyStd : S2W_TrustedStd.TrustedStd copyFn) (allocator : S2W_TrustedStd.Allocator A)
    (e1 e2 : S2W_D189Entry.Entry)
    (id : S2W_ExtractionBoundary.Program)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (state1 state2 final1 final2 : A) (post1 post2 : S2Trust.Heap (Nat → S2W_D189Entry.Record))
    (accepted1 : S2W_D189Wrappers.first native1 copyFn allocator e1 id data1 state1=ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 id data2 slot state2=ok (.Ok (post2,final2)))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B0) std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives geo) (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned) :
    S2W_EntryWriteHistory.payloadBytes S2W_ReturnedCheckpoint.encode
      (post1.payload (e1.heap.accounts 2).1) 1768=bytesOf saved.val ∧ post2=e2.heap ∧
    ∃ f s log,
      SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
        e1.first (e2.second S2W_D189Entry.secondSizes) saved f s ∧ RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
        (S2W_Observation.two (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
          id e1.first data1 (e2.second S2W_D189Entry.secondSizes) data2 slot) []=ok (.Ok saved,log) ∧
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
      (∀ (prior : AspisV8R19.MemoizedProgramLaw.Program Bytes State Unit)
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
            (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu))) ∧
      (∃ root2 : Array U8 32#usize,
      ∀ (history : S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val))
        (sameProof : bytesOf s.proof.val=bytesOf f.proof.val),
        SdkC_Source.readLog (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv f.proof run.p run.root) []).2=
          (AspisV8R19.MemoizedProgramLaw.eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ∧
        (AspisV8R19.MemoizedProgramLaw.eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2=true ∧
        SdkC_Source.readLog (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv s.proof tx2.p2 root2) []).2=
          (AspisV8R19.MemoizedProgramLaw.eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1 ∧
        (AspisV8R19.MemoizedProgramLaw.eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).2=true) ∧
      ∀ (decode : S2W_AuthenticatedInputs.HeaderDecode)
        (writerJoin : S2W_AuthenticatedInputs.CheckpointWriterConeJoin (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std) decode H f.semantic f.pub f.proof f.split)
        (readerJoin : S2W_AuthenticatedInputs.CheckpointReaderConeJoin (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std) decode H s.pub s.proof s.checkpoint)
        (history : S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val))
        (p2prime : S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub)
        (prior : AspisV8R19.MemoizedProgramLaw.Program Bytes State Unit),
        let trace := (AspisV8R19.MemoizedProgramLaw.eval H prior).1 ++
          AuS1_Recovery.log (Uni_Install.current ops reserved query geo) (F3M_CircleSource.install B0) std
            (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)
        AuS1_Finish.Collision H trace p q ∨
        ∃ after,CheckpointBytes5Effect.run
          (VTop_Checkpoint.digest (Tx1Q_Install.digest (SdkD_PairBatches.current a ops stage finish reserved query geo (F3M_CircleSource.install B0) std))) ()
          (CheckpointBytes5Join.stage reserved (F3K_CheckpointPreparedFields.writerPrepared out)
            (CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator
              {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) f.proof f.pub) []=ok (.Ok (tx2.p2,tx2.saved2),after) ∧
          CheckpointBytes5Inputs.observe after=(AspisV8R19.MemoizedProgramLaw.eval H
            (F3_Model.checkpoint i.physical i.stored p q (LiteralTranscript.erasePrefix
              (AspisV8R19.MemoizedProgramLaw.eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)
              input v)).1 := by
  have copied := PoolT_Write.accepted_verifier_writes_copy
    (SdkD_PairBatches.dictionary a ops stage finish reserved query geo (F3M_CircleSource.install B0) std)
    native1 native2 hashv extraction copyFn copyStd allocator e1 id data1 state1 final1 saved post1 accepted1
  have second := S2W_D189Wrappers.second_accepted native2 allocator e2 id data2 slot state2 final2 post2 accepted2
  refine ⟨copied.2.2.1,second.2,?_⟩
  exact F3Q_PairCheckpointLog.accepted a ops stage finish reserved query geo B0 std native1 native2 hashv extraction
    id e1.first (e2.second S2W_D189Entry.secondSizes) data1 data2 slot saved copied.1 second.1
    sha256 H p1 syscall w owner ports canonical domain multiply one inverse

#print axioms accepted
end AspisR1.F3Q_PoolPair
end
