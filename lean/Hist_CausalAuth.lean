import Hist_CommittedSdk
import Hist_PairExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_CausalAuth
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open Hist_Store Hist_RuntimeEntry S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_EntryWriteHistory S2W_ReturnedCheckpoint S2W_NativeConsolidation S2W_AuthenticatedInputs
open ClaimsUnrolledSdk MultiproofConeCanonical

/-- Local same-execution consumer. SourceCuts are the containing Program's
actual returned cuts. Runtime history and P2Prime are derived. Association of
that Program/Trace with a deployed experiment remains a separate obligation;
this theorem does not declare it by changing an opaque trust record. -/
theorem on_selected {A CoreError : Type}
    (sourceProgram : Program Bytes State Hist_PairExperiment.Pair) (iv : State) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H sourceProgram).1 ≤ Q)
    (H : Bytes → State)
    (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (stdClaims : ClaimsUnrolledFinish.StdCalls)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual ops reserved query geo B stdClaims))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (program : S2W_ExtractionBoundary.Program) (initial final : Store) (layout1 layout2 : Layout)
    (data1 : Slice U8) (state final1 : A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator (load initial layout1) program data1 state = ok (.Ok (saved,post1,final1)))
    (events : List S2X.AccountEvent)
    (trace : Trace (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims)
      program (commit initial (layout1.handles 2).1 saved) events final)
    (sameKey : (layout2.handles 6).1 = (layout1.handles 2).1)
    (cuts : SourceCuts (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims)
      (load initial layout1).first ((load final layout2).second secondSizes) saved
      (eval H sourceProgram).2.first (eval H sourceProgram).2.second)
    (decode : HeaderDecode)
    (writer : CheckpointWriterConeJoin
      (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims)
      decode H (eval H sourceProgram).2.first.semantic (eval H sourceProgram).2.first.pub
      (eval H sourceProgram).2.first.proof (eval H sourceProgram).2.first.split)
    (reader : CheckpointReaderConeJoin
      (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims)
      decode H (eval H sourceProgram).2.second.pub (eval H sourceProgram).2.second.proof
      (eval H sourceProgram).2.second.checkpoint) :
    BinRawByteCollisionTargets.event iv (Q+4) (eval H (Hist_PairExperiment.charged sourceProgram)) ∨
      ∃ runtime : S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload ((load initial layout1).heap.accounts 2).1) 1768)
        (bytesOf (eval H sourceProgram).2.second.checkpoint.val),
        runtime.key = (layout1.handles 2).1 ∧ runtime.events = events ∧
        bytesOf (eval H sourceProgram).2.second.proof.val = bytesOf (eval H sourceProgram).2.first.proof.val ∧
        bytesOf (eval H sourceProgram).2.second.pub.val = bytesOf (eval H sourceProgram).2.first.pub.val ∧
        bytesOf (eval H sourceProgram).2.second.checkpoint.val = bytesOf saved.val ∧
        (bytesOf saved.val).length = 1768 := by
  let pair := (eval H sourceProgram).2
  have native := (first_accepted native1 copy std allocator (load initial layout1) program data1 state final1 saved post1 accepted1).1
  have sourceAccepted := (extraction.stage1 program (load initial layout1).first data1).symm.trans native
  let savedHistory := Hist_CausalSdk.version adapter ops reserved query geo B stdClaims owner ports
    program initial final layout1 layout2 data1 saved sourceAccepted events trace sameKey pair.first pair.second cuts
  let runtime := Hist_CommittedSdk.version adapter ops reserved query geo B stdClaims owner ports
    native1 native2 hashv extraction copy std allocator program initial final layout1 layout2
    data1 state final1 saved post1 accepted1 events trace sameKey pair.first pair.second cuts
  rcases Hist_PairExperiment.binding_or_collision iv sourceProgram Q budget H with bad | p2prime
  · exact Or.inl bad
  · obtain ⟨proof,pub,checkpoint,size⟩ := authenticated_inputs _ decode H pair.first.semantic pair.first.pub
      pair.first.proof pair.second.pub pair.second.proof pair.second.checkpoint pair.first.split saved
      cuts.first cuts.second writer reader ⟨savedHistory⟩ p2prime
    exact Or.inr ⟨runtime,rfl,rfl,proof,pub,checkpoint,size⟩

#print axioms on_selected
#print on_selected
end AspisR1.Hist_CausalAuth
end
