import F3N_PairWriter
import F3N_ReaderNumeric
import F3N_SameRunWriter
import F3N_SameSecond
import F3N_SameOracle
import F3N_WriterOnRun
import F3N_SameRunTen
import F3N_SameRun
import PAln_Oracle
import RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_PairReadback
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation MultiproofConeCanonical

theorem accepted {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    ∃ f s log,
      SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
        accounts1 accounts2 saved f s ∧ RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
        (S2W_Observation.two (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
          id accounts1 data1 accounts2 data2 slot) []=ok (.Ok saved,log) ∧
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current a ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ (view : Slice U8) (i : F3_Model.Input),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        f.proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok run.root) ∧
      F3N_SourceInput.Facts f run.p H i ∧
      ∃ tx2 : Cons_Native.Witness,
      Cons_Native.Calls (AuS1_Install.base stage) finish reserved query geo
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)) ()
        s.pub s.proof s.checkpoint tx2 ∧
      Cons_NativeBuild.Aux reserved query geo
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)) ()
        s.pub s.proof s.checkpoint tx2 ∧
      ∃ out : AspisR1PublicPreparation.verifier.Prepared,
      AspisR1CurrentCaller.InstalledPreparation.currentPrepared out=run.p ∧
      (WAdm_NativeInstall.install (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)).op16
        (SdkD_PairBatches.current a ops stage finish reserved query geo B std) run.p
        {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} f.proof f.pub ()=ok saved ∧
      saved=Tx2N_Reader.writer H (bytesOf f.proof.val) (bytesOf f.pub.val) (F3L_SourcePrepared.numeric out)
        (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
          {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) ∧
      (∀ same : bytesOf s.checkpoint.val=bytesOf saved.val,
        CheckpointBytes4SavedFields.BodyMatches tx2.p2 tx2.saved2 (F3L_SourcePrepared.numeric out)
          (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
            {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) ∧
        CheckpointBytes5Output.accumulator tx2.saved2=
          CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
            {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}))) ∧
      ∀ (prior : AspisV8R19.MemoizedProgramLaw.Program Bytes State Unit)
        (same : bytesOf s.checkpoint.val=bytesOf saved.val)
        (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
        (p : OraclePortCompactDraft.Parsed)
        (parser : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some p),
        let trace := (AspisV8R19.MemoizedProgramLaw.eval H prior).1 ++
          AuS1_Recovery.log (Uni_Install.current ops reserved query geo) B std
            (SdkD_PairBatches.current a ops stage finish reserved query geo B std)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)
        ∃ frame, FS2.Duplex.Read trace frame ∧
          BinRawByteCollisionTargets.pred 3 frame=some (OraclePortBatchDraft.committedRoot p 2) ∧
          Cons_Ten.Outcome run H trace p := by
  obtain ⟨f,s,log,cuts,recorded,ran,run,view,i,range,copy,facts,tx2,calls,aux,out,output,writer,encoded,ten⟩ :=
    F3N_PairWriter.accepted a ops stage finish reserved query geo B std native1 native2 hashv extraction
      id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2 sha256 H p1 syscall w owner ports
  refine ⟨f,s,log,cuts,recorded,ran,run,view,i,range,copy,facts,tx2,calls,aux,out,output,writer,encoded,?_,ten⟩
  intro same
  have next : (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
      {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})).next=10 := by
    exact (Tx1Q_Control.fields _ reserved query geo _ ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run).2.2.1
  have reader := F3N_ReaderNumeric.saved_ten (AuS1_Install.base stage) reserved query _ ()
    s.checkpoint s.proof s.pub saved tx2.p2 tx2.saved2 H (bytesOf f.proof.val) (bytesOf f.pub.val)
    (F3L_SourcePrepared.numeric out) _ next same encoded calls.1
  exact ⟨reader.1,reader.2.1⟩

#print axioms accepted
end AspisR1.F3N_PairReadback
end
