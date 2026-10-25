import Hiq_NativeAccountDriver
import Hiq_CarrierIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_CanonicalAccountDriver
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
          i = Hiq_CanonicalCarrier.input f.pub f.proof ∧ Port1_StoredCarrier.Carried i ∧
          i.statement.pubBytes = bytesOf f.pub.val ∧ i.stored = bytesOf f.proof.val ∧
          (eval H (DrvC_Implementation.driver r i)).2 = true ∧
          ¬ (∀ j, (eval H (DrvC_Implementation.driver r j)).2 = false)) := by
  obtain ⟨f,s,v,cuts,get,validate,encode,associated,binding⟩ :=
    Hiq_NativeAccountDriver.accepted c hashv copy allocator id adversary chooseSecond keyLaw
      Q0 Q1 prefixBound choiceBound trustedCopy native1 native2 extraction sha256 H p1 syscall saved post1 post2 final1 final2
      accepted1 accepted2 initial actions l1 l2 load1 load2 sameKey project
  refine ⟨f,s,v,cuts,get,validate,encode,associated,?_⟩
  rcases binding with bad | ⟨old,oldPublic,oldProof,yes,_⟩
  · exact Or.inl bad
  · right
    have fit := DrvC_PublicCarrier.fits f.pub (DrvC_PublicCarrier.public_length r _ _ saved f s cuts)
    let i := Hiq_CanonicalCarrier.input f.pub f.proof
    have pub : i.statement.pubBytes = bytesOf f.pub.val := Hiq_CanonicalCarrier.public_bytes f.pub f.proof fit
    have stored : i.stored = bytesOf f.proof.val := rfl
    have programs := DrvC_Implementation.physical r i old (pub.trans oldPublic.symm) (stored.trans oldProof.symm)
    have accepted : (eval H (DrvC_Implementation.driver r i)).2 = true := by rw [programs]; exact yes
    refine ⟨i,rfl,Hiq_CanonicalCarrier.carried _ _,pub,stored,accepted,?_⟩
    intro rejects
    have no := (rejects i).symm.trans accepted
    cases no

#print axioms accepted
set_option pp.proofs false in
#print accepted
end AspisR1.Hiq_CanonicalAccountDriver
end
