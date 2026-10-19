import RawCompiledRunWordStabilityV8

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCompiledTranscriptRoundAlignment

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.LiteralTranscript

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

attribute [local irreducible] RawCutWordsFromView.buildWords

private theorem valid_enrichMessage (w : CanonicalCutEnrichedTranscript.Words)
    (j : Nat) (m : LiteralTranscript.Message) :
    LiteralTranscript.valid j (enrichMessage w m) ↔ LiteralTranscript.valid j m := by
  cases m with
  | initial root word =>
      by_cases hj : j = 0
      · subst j
        simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hj]
  | payload bytes => simp [LiteralTranscript.valid, enrichMessage]
  | c2 bytes word =>
      by_cases hj : j = 2
      · subst j
        simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hj]
  | second bytes word =>
      by_cases hj : j = 30
      · subst j
        simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hj]

/-- For the compiled prover, the protocol's actual round list is exactly the
enrichment of the original execution's rounds by the words recovered from
the compiled run's recorded log. This is the annotation/round alignment needed
by the recorded extractor; the two validity hypotheses are precisely those
used to identify compiled-log recovery with the compiler's retained builder. -/
theorem compiled_rounds_eq_enrich_recoveredWords
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) (n : Nat)
    (hvalidOriginal : ∀ j, j ≤ 30 → LiteralTranscript.valid j
      ((eval H (experiment P (verifier decoder d))).2.1.2 j)) :
    ((LiteralByteProtocol.protocol decoder).transcript H
      (eval H (experiment (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))).2.1.1
      (eval H (experiment (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))).2.1.2 n).rounds =
    enrichRounds
      (RawCutWordsFromRunExecutable.wordsFromRun
        (eval H (experiment (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
          (verifier decoder d))))
      ((LiteralByteProtocol.protocol decoder).transcript H
        (eval H (experiment P (verifier decoder d))).2.1.1
        (eval H (experiment P (verifier decoder d))).2.1.2 n).rounds := by
  let original := eval H (experiment P (verifier decoder d))
  let annotated := eval H (experiment
    (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
    (verifier decoder d))
  have hrun : annotated =
      let v := original
      (v.1 ++ (eval H (verifier decoder d v.2.1.1 v.2.1.2)).1,
        ((v.2.1.1, RawCutTranscriptRun.proof (RawCutWordsFromView.buildWords decoder v)
          v.2.1.2), v.2.2)) := by
    dsimp only [annotated, original]
    exact compiled_experiment_eval decoder d (RawCutWordsFromView.buildWords decoder) P H
  have hproof : annotated.2.1.2 =
      RawCutTranscriptRun.proof (RawCutWordsFromView.buildWords decoder original)
        original.2.1.2 := by
    exact congrArg (fun v : RawCutProverCompiler.RunView => v.2.1.2) hrun
  have hvalidCompiled : ∀ j, j ≤ 30 → LiteralTranscript.valid j (annotated.2.1.2 j) := by
    intro j hj
    rw [hproof]
    change LiteralTranscript.valid j
      (enrichMessage (RawCutWordsFromView.buildWords decoder original)
        (original.2.1.2 j))
    rw [valid_enrichMessage]
    simpa only [original] using hvalidOriginal j hj
  have hwords := RawCompiledRunWordStability.wordsFromRun_compiled_eq_retainedBuildWords
    decoder d P H hvalidOriginal hvalidCompiled
  have hwords' : RawCutWordsFromRunExecutable.wordsFromRun annotated =
      RawCutWordsFromView.buildWords decoder original := by
    simpa only [annotated, original] using hwords
  have htrans := RawCutTranscriptRun.transcript_eq decoder
    (RawCutWordsFromView.buildWords decoder original) H original.2.1.1 original.2.1.2 n
  calc
    _ = enrichRounds (RawCutWordsFromView.buildWords decoder original)
        ((LiteralByteProtocol.protocol decoder).transcript H original.2.1.1
          original.2.1.2 n).rounds := by
      change ((LiteralByteProtocol.protocol decoder).transcript H
        annotated.2.1.1 annotated.2.1.2 n).rounds = _
      rw [hrun]
      exact congrArg (fun p : LiteralTranscript.Prefix => p.rounds) htrans
    _ = _ := by rw [← hwords']

#print axioms compiled_rounds_eq_enrich_recoveredWords
end AspisR1.RawCompiledTranscriptRoundAlignment
end
