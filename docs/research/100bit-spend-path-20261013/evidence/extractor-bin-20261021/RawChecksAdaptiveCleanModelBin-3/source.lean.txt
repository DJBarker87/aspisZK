import RawFullPublicSelection
import RawRecordedActualAdaptiveFailureBoundBin
import LiteralTableWordChoiceBin
import RawCompiledChecksOriginalScheduleBin
import RawCutWordsFromRunExecutableBin
import LiteralNoHitFromTranscriptAlignment
import RawChecksHitFromTransport

/-! Binary extractor consumer: compiler metadata, executable recovery, and
causal table decoder all use the binary recovery modules. M9's generic
no-hit transport and collision envelope are otherwise unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.RawChecksAdaptiveCleanModelBin

open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutWordsFromRunExecutableBin
open AspisR1.RawCutTranscriptRun
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.RawRecordedOracleExtractionMassBin
open AspisR1.RawAdaptiveLiteralDecoder
open AspisR1.RawChecksHitFromTransport
open AspisR1.RawAdaptiveClassifierHitDensity
open AspisR1.GenericNoHit
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling

attribute [local irreducible] RawCutProverCompiler.compiled
  BinCompiledRunWordStability.wordsFromRun R0C.V3.hitsChain3 GenericNoHit.hitFrom
  RawRecordedOracleExtractionMassBin.CleanAcceptedModel
  AcceptedAdaptiveFiatShamir.experiment

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

private theorem valid_enrichMessage (w : CanonicalCutEnrichedTranscript.Words)
    (i : Nat) (m : LiteralTranscript.Message) :
    LiteralTranscript.valid i (enrichMessage w m) ↔ LiteralTranscript.valid i m := by
  cases m with
  | initial root word =>
      by_cases hi : i = 0
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]
  | payload bytes => simp [LiteralTranscript.valid, enrichMessage]
  | c2 bytes word =>
      by_cases hi : i = 2
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]
  | second bytes word =>
      by_cases hi : i = 30
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]

private theorem proof_idempotent (w : CanonicalCutEnrichedTranscript.Words)
    (pf : LiteralProtocol.Proof) :
    RawCutTranscriptRun.proof w (RawCutTranscriptRun.proof w pf) =
      RawCutTranscriptRun.proof w pf := by
  funext i
  cases h : pf i <;> simp [RawCutTranscriptRun.proof, enrichMessage, h]

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

private theorem chains_read (decoder : LiteralByteProtocol.Decoder) :
    ChainsRead (LiteralByteProtocol.protocol decoder) := by
  intro i P m hi
  change firstCell (ProgramSamplerMap.map Addr.toBytes
    (LiteralTranscript.samp i P m)) ≠ none
  rw [firstCell_map]
  have hn : firstCell (LiteralTranscript.samp i P m) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  cases h : firstCell (LiteralTranscript.samp i P m) with
  | none => exact absurd h hn
  | some a => simp

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : Sampler I A C) (a : I)
    (ha : firstCell s = some a) :
    a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [firstCell, Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [firstCell, Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

private theorem verifier_reads (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool) :
    ReadsChains (LiteralByteProtocol.protocol decoder) (verifier decoder d) := by
  intro H pub pf i a hi ha
  have hread := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf i hi a
  change a ∈ (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) pub pf)).1.map Prod.fst
  apply hread
  exact firstCell_mem H _ a ha

attribute [local irreducible] RawCutProverCompiler.verifier LiteralByteProtocol.protocol

private theorem pair_eq_of_components {α β : Type} {a c : α} {b d : β}
    (h₁ : a = c) (h₂ : b = d) : (a, b) = (c, d) := by
  cases h₁
  cases h₂
  rfl

private theorem not_predicate_transport {α : Type} (P : α → Prop)
    {a b : α} (h : a = b) (hb : ¬ P b) : ¬ P a := by
  cases h
  exact hb

/-- The executable extractor recovers exactly the word metadata retained by
the binary compiler. Equality is total, including failed/missing recoveries. -/
theorem extractor_word_alignment
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State)
    (checks : let run := eval H (experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P) (verifier decoder d))
      LiteralAcceptanceTerminal.Checks run.2.1.1
        ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 33).rounds) :
    let orig := eval H (experiment P (verifier decoder d))
    let run := eval H (experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P) (verifier decoder d))
    wordsFromRun run = BinCompiledRunWordStability.wordsFromRun decoder orig ∧
      RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2 = run.2.1.2 := by
  let orig := eval H (experiment P (verifier decoder d))
  let run := eval H (experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P) (verifier decoder d))
  have hrunRaw : run = eval H (experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P) (verifier decoder d)) := rfl
  have hpf : run.2.1.2 = RawCutTranscriptRun.proof
      (BinCompiledRunWordStability.wordsFromRun decoder orig) orig.2.1.2 := by
    dsimp only [run, orig]
    rw [compiled_experiment_eval]
  have hvalidOrig : ∀ j, j ≤ 30 → LiteralTranscript.valid j (orig.2.1.2 j) := by
    exact RawCompiledChecksOriginalScheduleBin.checks_force_original_constructor_schedule
      decoder d P H orig run rfl hrunRaw checks
  have hvalidRun : ∀ j, j ≤ 30 → LiteralTranscript.valid j (run.2.1.2 j) := by
    intro j hj
    rw [hpf]
    exact (valid_enrichMessage (BinCompiledRunWordStability.wordsFromRun decoder orig) j
      (orig.2.1.2 j)).2 (hvalidOrig j hj)
  have hvalidRunRaw : ∀ j, j ≤ 30 → LiteralTranscript.valid j
      ((eval H (RawCutProverCompiler.experiment
        (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
        (verifier decoder d))).2.1.2 j) := by
    simpa only [← hrunRaw] using hvalidRun
  have hwordsRaw := (RawCutWordsFromRunExecutableBin.wordsFromRun_eq_buildWords
    decoder _ hvalidRunRaw).trans
    (BinCompiledRunWordStability.wordsFromRun_compiled_eq_retainedBuildWords decoder d P H)
  have hwordsRun : wordsFromRun run =
      BinCompiledRunWordStability.wordsFromRun decoder orig := by
    simpa only [← hrunRaw] using hwordsRaw
  have hpfFixed : RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2 = run.2.1.2 := by
    rw [hwordsRun, hpf]
    exact proof_idempotent (BinCompiledRunWordStability.wordsFromRun decoder orig) orig.2.1.2
  exact ⟨hwordsRun, hpfFixed⟩

/-- Checked acceptance plus absence of the actual lazy-injection collision and
decoded-chain events supplies the exact clean-model premise used by the
recorded shared-oracle failure theorem. Word recovery is aligned through the
compiled-run stability theorem; no fresh/shared-ROM identification is made. -/
theorem clean_model_of_checked_acceptance_no_hit
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (κ : Nat → ℚ) (Q : Nat)
    (hchecks : ∀ H : Bytes → State,
      FS2.accepts (eval H (experiment P (verifier decoder d))) →
      LiteralAcceptanceTerminal.Checks
        (eval H (experiment
          (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
          (verifier decoder d))).2.1.1
        (((LiteralByteProtocol.protocol decoder).transcript H
          (eval H (experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.1
          (eval H (experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.2 33).rounds))
    (inj : AcceptedAdaptiveFiatShamir.LazyInj
      (LiteralByteProtocol.protocol decoder)
      (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
        LiteralTableWordChoiceBin.choose)
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
      (verifier decoder d) κ Q)
    (exp : RawRecordedOracleExtractionMassBin.Experiment)
    (hexp : exp = AcceptedAdaptiveFiatShamir.experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
      (verifier decoder d))
    (hit : RawCutProverCompiler.RunView → Prop)
    (hHit : ∀ run, hit run ↔ inj.Coll run ∨ hitsChain3
      (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
        LiteralTableWordChoiceBin.choose)
      RawAdaptiveClassifierHitDensity.classifier emptyTable run.1) :
    CleanAcceptedModel decoder
      exp
      hit := by
  unfold RawRecordedOracleExtractionMassBin.CleanAcceptedModel
  intro H run ha hnot
  have hexpRaw : exp = RawCutProverCompiler.experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
      (verifier decoder d) := by
    rw [hexp]
    unfold AcceptedAdaptiveFiatShamir.experiment RawCutProverCompiler.experiment
    rfl
  have hrunAccepted : run = eval H (AcceptedAdaptiveFiatShamir.experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
      (verifier decoder d)) := by
    change eval H exp = _
    rw [hexp]
  let orig := eval H (experiment P (verifier decoder d))
  have hexpCompiler : AcceptedAdaptiveFiatShamir.experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
      (verifier decoder d) = RawCutProverCompiler.experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
      (verifier decoder d) := by
    unfold AcceptedAdaptiveFiatShamir.experiment RawCutProverCompiler.experiment
    rfl
  have hrunRaw : run = eval H (RawCutProverCompiler.experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
      (verifier decoder d)) := by
    change eval H exp = _
    rw [hexpRaw]
  have hrun : run =
      let v := orig
      (v.1 ++ (eval H (verifier decoder d v.2.1.1 v.2.1.2)).1,
        ((v.2.1.1, RawCutTranscriptRun.proof
          (BinCompiledRunWordStability.wordsFromRun decoder v) v.2.1.2), v.2.2)) := by
    calc
      run = eval H (RawCutProverCompiler.experiment
        (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
        (verifier decoder d)) := hrunRaw
      _ = _ := by
        simpa only [orig] using compiled_experiment_eval decoder d
          (BinCompiledRunWordStability.wordsFromRun decoder) P H
  have hpub : run.2.1.1 = orig.2.1.1 := by rw [hrun]
  have hpf : run.2.1.2 = RawCutTranscriptRun.proof
      (BinCompiledRunWordStability.wordsFromRun decoder orig) orig.2.1.2 := by rw [hrun]
  have haccOriginal : FS2.accepts orig := by
    change orig.2.2 = true
    have haccRun : run.2.2 = true := ha
    rw [hrun] at haccRun
    exact haccRun
  have checks : LiteralAcceptanceTerminal.Checks run.2.1.1
      ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 33).rounds := by
    simpa only [← hrunRaw] using hchecks H haccOriginal
  have hvalidOrig : ∀ j, j ≤ 30 → LiteralTranscript.valid j (orig.2.1.2 j) := by
    exact RawCompiledChecksOriginalScheduleBin.checks_force_original_constructor_schedule
      decoder d P H orig run rfl hrunRaw checks
  have hvalidRun : ∀ j, j ≤ 30 → LiteralTranscript.valid j (run.2.1.2 j) := by
    intro j hj
    rw [hpf]
    exact (valid_enrichMessage (BinCompiledRunWordStability.wordsFromRun decoder orig) j
      (orig.2.1.2 j)).2 (hvalidOrig j hj)
  have hvalidRunRaw : ∀ j, j ≤ 30 → LiteralTranscript.valid j
      ((eval H (RawCutProverCompiler.experiment
        (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
        (verifier decoder d))).2.1.2 j) := by
    simpa only [← hrunRaw] using hvalidRun
  have hwordsRaw := (RawCutWordsFromRunExecutableBin.wordsFromRun_eq_buildWords
    decoder _ hvalidRunRaw).trans
    (BinCompiledRunWordStability.wordsFromRun_compiled_eq_retainedBuildWords decoder d P H)
  have hwordsRun : wordsFromRun run =
      BinCompiledRunWordStability.wordsFromRun decoder orig := by
    simpa only [← hrunRaw] using hwordsRaw
  have hpfFixed : RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2 = run.2.1.2 := by
    rw [hwordsRun, hpf]
    exact proof_idempotent (BinCompiledRunWordStability.wordsFromRun decoder orig) orig.2.1.2
  have hnoRaw : ¬ hitFrom LiteralClassifier.bad run.2.1.1 []
      ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 33).rounds := by
    have hnotEvent : ¬ (inj.Coll run ∨ hitsChain3
        (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
          LiteralTableWordChoiceBin.choose)
        RawAdaptiveClassifierHitDensity.classifier emptyTable run.1) := by
      intro he
      exact hnot ((hHit run).2 he)
    have hcoll : ¬ inj.Coll run := by
      intro hc
      exact hnotEvent (Or.inl hc)
    have hchain : ¬ hitsChain3
        (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
          LiteralTableWordChoiceBin.choose)
        RawAdaptiveClassifierHitDensity.classifier emptyTable run.1 := by
      intro hc
      exact hnotEvent (Or.inr hc)
    have hchain' : ¬ hitsChain3
        (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
          LiteralTableWordChoiceBin.choose)
        (fun p m _T c => LiteralClassifier.bad p m c) emptyTable run.1 := by
      change ¬ hitsChain3
        (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
          LiteralTableWordChoiceBin.choose)
        (fun p m _T c => LiteralClassifier.bad p m c) emptyTable run.1 at hchain
      exact hchain
    have haccAccepted : FS2.accepts
        (eval H (AcceptedAdaptiveFiatShamir.experiment
          (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
          (verifier decoder d))) := by
      change (eval H (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
        (verifier decoder d))).2.2 = true
      rw [← hrunAccepted]
      exact ha
    have hnoRawAccepted : ¬ hitFrom LiteralClassifier.bad
        (eval H (AcceptedAdaptiveFiatShamir.experiment
          (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
          (verifier decoder d))).2.1.1 []
        ((LiteralByteProtocol.protocol decoder).transcript H
          (eval H (AcceptedAdaptiveFiatShamir.experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.1
          (eval H (AcceptedAdaptiveFiatShamir.experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.2 33).rounds := by
      intro hraw
      have hcollAccepted : ¬ inj.Coll (eval H (AcceptedAdaptiveFiatShamir.experiment
          (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
          (verifier decoder d))) := by
        intro hh
        exact hcoll (hrunAccepted.symm ▸ hh)
      have hr : (LiteralByteProtocol.protocol decoder).r = 33 := by
        unfold LiteralByteProtocol.protocol
        rfl
      have hrawR : hitFrom LiteralClassifier.bad
          (eval H (AcceptedAdaptiveFiatShamir.experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.1 []
          ((LiteralByteProtocol.protocol decoder).transcript H
            (eval H (AcceptedAdaptiveFiatShamir.experiment
              (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
              (verifier decoder d))).2.1.1
            (eval H (AcceptedAdaptiveFiatShamir.experiment
              (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
              (verifier decoder d))).2.1.2 (LiteralByteProtocol.protocol decoder).r).rounds := by
        rw [hr]
        exact hraw
      have hc := AspisR1.LiteralAdaptiveClassifierHitToDecodedChain.accepted_hit_implies_decoded_chain
        (pr := LiteralByteProtocol.protocol decoder)
        (bad := LiteralClassifier.bad)
        (dec := RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
          LiteralTableWordChoiceBin.choose)
        (P := compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
        (V := verifier decoder d) (κ := κ)
        (Qtot := Q) (inj := inj) (hreads := chains_read decoder)
        (hV := verifier_reads decoder d) (H := H) (hcoll := hcollAccepted)
        (hacc := haccAccepted) (hhit := hrawR)
      exact hchain' (hrunAccepted.symm ▸ hc)
    have hroundsRaw :
        ((LiteralByteProtocol.protocol decoder).transcript H
          (eval H (AcceptedAdaptiveFiatShamir.experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.1
          (eval H (AcceptedAdaptiveFiatShamir.experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.2 33).rounds =
        ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 33).rounds := by
      rw [← hrunAccepted]
    have hnoRunRaw : ¬ hitFrom LiteralClassifier.bad run.2.1.1 []
        ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 33).rounds := by
      intro hbad
      have hpubAccepted : run.2.1.1 =
          (eval H (AcceptedAdaptiveFiatShamir.experiment
            (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
            (verifier decoder d))).2.1.1 := by
        exact congrArg (fun z : RawCutProverCompiler.RunView => z.2.1.1) hrunAccepted
      have hmove := hitFrom_transport LiteralClassifier.bad hpubAccepted hroundsRaw.symm
      exact hnoRawAccepted (hmove.mp hbad)
    exact hnoRunRaw
  refine ⟨?_, ?_⟩
  · rw [hpfFixed]
    exact checks
  · rw [hpfFixed]
    exact hnoRaw

#print axioms valid_enrichMessage
#print axioms proof_idempotent
#print axioms firstCell_map
#print axioms chains_read
#print axioms firstCell_mem
#print axioms verifier_reads
#print axioms pair_eq_of_components
#print axioms not_predicate_transport
#print axioms extractor_word_alignment
#print axioms clean_model_of_checked_acceptance_no_hit
end AspisR1.RawChecksAdaptiveCleanModelBin
end
