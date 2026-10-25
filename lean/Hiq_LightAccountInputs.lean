import Hiq_DrvExperiment
import Hiq_LightAuthenticated
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_LightAccountInputs
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

theorem accepted
    (keyLaw : (sdk c).op36 = Hist_Authority.keyEq)
    (Q0 Q1 : Nat) (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (trustedCopy : S2W_TrustedStd.TrustedStd copy)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (accepted1 : let input := (eval H adversary).2
      first native1 copy allocator input.entry id input.data input.state = ok (.Ok (saved,post1,final1)))
    (accepted2 : let input := (eval H adversary).2
      let next := (eval H (chooseSecond input saved post1 final1)).2
      second native2 allocator next.entry id next.data next.slot next.state = ok (.Ok (post2,final2)))
    (initial final : Hist_Store.Store) (l1 l2 : Hist_RuntimeEntry.Layout)
    (load1 : (eval H adversary).2.entry = Hist_RuntimeEntry.load initial l1)
    (load2 : (eval H (chooseSecond (eval H adversary).2 saved post1 final1)).2.entry = Hist_RuntimeEntry.load final l2)
    (events : List S2X.AccountEvent)
    (trace : Hist_Store.Trace (sdk c) id (Hist_RuntimeEntry.commit initial (l1.handles 2).1 saved) events final)
    (sameKey : (l2.handles 6).1 = (l1.handles 2).1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    let input := (eval H adversary).2
    let next := (eval H (chooseSecond input saved post1 final1)).2
    ∃ f s v, SourceCuts (sdk c) input.entry.first (next.entry.second secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (sdk c) id (next.entry.second secondSizes)
        next.data next.slot = ok (.Ok v) ∧
      (sdk c).op22 v.statement = ok (.Ok s.encoded) ∧
      Hiq_ByteSelection.select (sdk c) id (eval H (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)).2 =
        Hist_PairExperiment.select ⟨f,s⟩ ∧
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_DrvExperiment.joint c hashv copy allocator id adversary chooseSecond project)) ∨
        (bytesOf s.proof.val = bytesOf f.proof.val ∧ bytesOf s.pub.val = bytesOf f.pub.val ∧
          bytesOf s.checkpoint.val = bytesOf saved.val ∧ saved.val.length = 1768)) := by
  let input := (eval H adversary).2
  let next := (eval H (chooseSecond input saved post1 final1)).2
  obtain ⟨f,s,v,cuts,get,validate,encode,associated,binding⟩ :=
    Hiq_AccountBinding.accepted c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish c.reserved c.query c.geometry
      c.boundaries c.std hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound
      trustedCopy native1 native2 extraction sha256 H p1 syscall saved post1 post2 final1 final2 accepted1 accepted2 project
  refine ⟨f,s,v,cuts,get,validate,encode,associated,?_⟩
  rcases binding with bad | good
  · exact Or.inl bad
  · right
    have native := (first_accepted native1 copy trustedCopy allocator input.entry id input.data input.state final1 saved post1 accepted1).1
    have source := (extraction.stage1 id input.entry.first input.data).symm.trans native
    have loadedSource : AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c) id
        (Hist_RuntimeEntry.load initial l1).first input.data = ok (.Ok saved) := by
      simpa only [input,load1] using source
    have loadedCuts : SourceCuts (sdk c) (Hist_RuntimeEntry.load initial l1).first
        ((Hist_RuntimeEntry.load final l2).second secondSizes) saved f s := by
      rw [gexp_dictionary]
      simpa only [load1,load2] using cuts
    have oracle := S2W_DigestExtraction.native_oracle _ native1 native2 hashv extraction sha256 H p1 syscall
    exact Hiq_LightAuthenticated.inputs c keyLaw id initial final l1 l2 input.data saved loadedSource
      events trace sameKey f s loadedCuts H oracle good

#print axioms accepted
set_option pp.proofs false in
#print accepted
end AspisR1.Hiq_LightAccountInputs
end
