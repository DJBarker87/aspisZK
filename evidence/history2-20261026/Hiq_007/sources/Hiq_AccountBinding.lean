import Hiq_Association
import Hiq_JointBinding
import GExq_AccountAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_AccountBinding
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
variable {A F C : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)

include prefixBound choiceBound

theorem accepted
    (trustedCopy : S2W_TrustedStd.TrustedStd copy)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter current stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (accepted1 : let input := (eval H adversary).2
      first native1 copy allocator input.entry id input.data input.state = ok (.Ok (saved,post1,final1)))
    (accepted2 : let input := (eval H adversary).2
      let next := (eval H (chooseSecond input saved post1 final1)).2
      second native2 allocator next.entry id next.data next.slot next.state = ok (.Ok (post2,final2)))
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    let input := (eval H adversary).2
    let next := (eval H (chooseSecond input saved post1 final1)).2
    let installed := GExq_Caller.sdk adapter current stage finish reserved query geo B std
    let source := program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond
    ∃ f s v, SourceCuts installed input.entry.first (next.entry.second secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 installed id (next.entry.second secondSizes)
        next.data next.slot = ok (.Ok v) ∧
      installed.op22 v.statement = ok (.Ok s.encoded) ∧
      Hiq_ByteSelection.select installed id (eval H source).2 = Hist_PairExperiment.select ⟨f,s⟩ ∧
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hist_JointCharge.joint source project (Hiq_ByteSelection.select installed id))) ∨
        S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub) := by
  let input := (eval H adversary).2
  let next := (eval H (chooseSecond input saved post1 final1)).2
  have n1 := (first_accepted native1 copy trustedCopy allocator input.entry id input.data input.state final1 saved post1 accepted1).1
  have n2 := (second_accepted native2 allocator next.entry id next.data next.slot next.state final2 post2 accepted2).1
  have src1 := (extraction.stage1 id input.entry.first input.data).symm.trans n1
  have src2 := (extraction.stage2 id (next.entry.second secondSizes) next.data next.slot).symm.trans n2
  have ran := GExq_AccountAccepted.accepted adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond
    native1 native2 extraction sha256 H p1 syscall saved post1 post2 final1 final2 accepted1 accepted2
  obtain ⟨f,s,v,cuts,get,validate,encode,selected⟩ := Hiq_Association.source _ id input next
    (ok (.Ok (saved,post1,final1))) (ok (.Ok (post2,final2))) saved src1 src2
  have association : Hiq_ByteSelection.select _ id
      (eval H (program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond)).2 =
      Hist_PairExperiment.select ⟨f,s⟩ := by
    rw [ran]
    exact selected
  refine ⟨f,s,v,cuts,get,validate,encode,association,?_⟩
  have bound := RawJ_CollisionBudget.first_reads adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond
    Q0 Q1 prefixBound choiceBound
  have binding := Hiq_JointBinding.binding_or_collision SelectedTranscriptParams.params.iv
    (program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond)
    project (Hiq_ByteSelection.select _ id) (Q0+Q1+1921) bound H
  rw [association] at binding
  simpa only [show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega,
    Hist_PairExperiment.select] using binding

#print axioms accepted
#print accepted
end AspisR1.Hiq_AccountBinding
end
