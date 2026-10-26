import PoolT_Write
import F3N_SameRunAccumulator
import F3N_TenDiscovered
import F3N_SameRun
import PAln_Oracle
import RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_PoolAccumulator
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation MultiproofConeCanonical
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2W_ReturnedCheckpoint

theorem accepted {F C A : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (copyStd : TrustedStd copy) (allocator : Allocator A) (e1 e2 : Entry)
    (id : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 id data1 state1=ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 id data2 slot state2=ok (.Ok (post2,final2)))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives geo) (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned) :
    S2W_EntryWriteHistory.payloadBytes S2W_ReturnedCheckpoint.encode
      (post1.payload (e1.heap.accounts 2).1) 1768=bytesOf saved.val ∧ post2=e2.heap ∧
    ∃ f s log,
      SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
        e1.first (e2.second secondSizes) saved f s ∧ RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
        (S2W_Observation.two (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
          id e1.first data1 (e2.second secondSizes) data2 slot) []=ok (.Ok saved,log) ∧
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current a ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ (view : Slice U8) (i : F3_Model.Input),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        f.proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok run.root) ∧
      F3N_SourceInput.Facts f run.p H i ∧
      ∀ (prior : AspisV8R19.MemoizedProgramLaw.Program Bytes State Unit)
        (same : bytesOf s.checkpoint.val=bytesOf saved.val)
        (sameProof : bytesOf s.proof.val=bytesOf f.proof.val),
        let trace := (AspisV8R19.MemoizedProgramLaw.eval H prior).1 ++
          AuS1_Recovery.log (Uni_Install.current ops reserved query geo) B std
            (SdkD_PairBatches.current a ops stage finish reserved query geo B std)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)
        let tr := LiteralTranscript.erasePrefix (AspisV8R19.MemoizedProgramLaw.eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
        (∃ p q input,OraclePortStoredParserC4.parseReached i.stored tr=some p ∧
          OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some input ∧
          AuS1_Finish.Collision H trace p q) ∨
        (∃ p q input,OraclePortStoredParserC4.parseReached i.stored tr=some p ∧
          OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some input ∧
          CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
            {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})=
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model input.data
              (SelectedChallengeMap.rhoOf input.rho) q)).accumulator) := by
  have copied := PoolT_Write.accepted_verifier_writes_copy
    (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std) native1 native2 hashv extraction
    copy copyStd allocator e1 id data1 state1 final1 saved post1 accepted1
  have second := S2W_D189Wrappers.second_accepted native2 allocator e2 id data2 slot state2 final2 post2 accepted2
  apply And.intro copied.2.2.1
  apply And.intro second.2
  exact F3N_SameRunAccumulator.accepted a ops stage finish reserved query geo B std native1 native2
    hashv extraction id e1.first (e2.second secondSizes) data1 data2 slot saved copied.1 second.1
    sha256 H p1 syscall w ports canonical domain multiply one inverse

#print axioms accepted
end AspisR1.F3N_PoolAccumulator
end
