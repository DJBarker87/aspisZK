import Hiq_LightAccountDriver
import Hiq_NativeHistory
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_NativeAccountDriver
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))

local notation "r" => (DrvC_FirstConstants.configuration c)

theorem accepted
    (keyLaw : (sdk r).op36 = Hist_Authority.keyEq)
    (Q0 Q1 : Nat) (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (trustedCopy : S2W_TrustedStd.TrustedStd copy)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk r) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (accepted1 : let input := (eval H adversary).2
      first native1 copy allocator input.entry id input.data input.state = ok (.Ok (saved,post1,final1)))
    (accepted2 : let input := (eval H adversary).2
      let next := (eval H (chooseSecond input saved post1 final1)).2
      second native2 allocator next.entry id next.data next.slot next.state = ok (.Ok (post2,final2)))
    (initial : Hist_Store.Store) (actions : List (Hiq_NativeAction.Action A)) (l1 l2 : Hist_RuntimeEntry.Layout)
    (load1 : (eval H adversary).2.entry = Hist_RuntimeEntry.load initial l1)
    (load2 : (eval H (chooseSecond (eval H adversary).2 saved post1 final1)).2.entry = Hist_RuntimeEntry.load (Hiq_NativeHistory.run native1 copy allocator id (Hist_RuntimeEntry.commit initial (l1.handles 2).1 saved) actions).1 l2)
    (sameKey : (l2.handles 6).1 = (l1.handles 2).1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    let input := (eval H adversary).2
    let next := (eval H (chooseSecond input saved post1 final1)).2
    ∃ f s v, SourceCuts (sdk r) input.entry.first (next.entry.second secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (sdk r) id (next.entry.second secondSizes)
        next.data next.slot = ok (.Ok v) ∧
      (sdk r).op22 v.statement = ok (.Ok s.encoded) ∧
      Hiq_ByteSelection.select (sdk r) id (eval H (Hiq_DrvExperiment.source r hashv copy allocator id adversary chooseSecond)).2 =
        Hist_PairExperiment.select ⟨f,s⟩ ∧
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_DrvExperiment.joint r hashv copy allocator id adversary chooseSecond project)) ∨
        ∃ i : OraclePortStoredExperimentC4.Input,
          i.statement.pubBytes = bytesOf f.pub.val ∧ i.stored = bytesOf f.proof.val ∧
          (eval H (DrvC_Implementation.driver r i)).2 = true ∧
          ¬ (∀ j, (eval H (DrvC_Implementation.driver r j)).2 = false)) := by
  exact Hiq_LightAccountDriver.accepted c hashv copy allocator id adversary chooseSecond keyLaw
    Q0 Q1 prefixBound choiceBound trustedCopy native1 native2 extraction sha256 H p1 syscall saved post1 post2 final1 final2
    accepted1 accepted2 initial _ l1 l2 load1 load2 _
    (Hiq_NativeHistory.classified native1 copy allocator id (sdk r) keyLaw
      (fun id accounts data => (extraction.stage1 id accounts data).symm) trustedCopy _ actions) sameKey project

#print axioms accepted
set_option pp.proofs false in
#print accepted
end AspisR1.Hiq_NativeAccountDriver
end
