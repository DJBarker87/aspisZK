import OraclePortReplay

/-! Reuse the arity-independent recording compiler, frame replay, and
commitment-cut equality; replace only the recovery maps by binary maps.
Mirrors RawCompiledRunWordStabilityV8.lean:42 and :165 without the old
executable eight-way recovery adapter. No source verifier refinement claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortWords
open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RawCutProverCompiler (Prover RunView experiment)
open RawCutWordsFromView (frame frameFromView rootFrom)
open OraclePortReplay
open OracleDecisionFeasibilityCore (Decision verifier)
open OracleDecisionFeasibilityCompiler (compiled compiled_experiment_eval commitment_cut_eq)
open CanonicalCutEnrichedTranscript (Words)

abbrev wordsFromRun := BinCompiledRunWordStability.wordsFromRun

/-- Compiler replay cannot change binary words recovered at the three cuts.
No collision premise is needed: the cuts themselves are literally equal. -/
theorem wordsFromRun_compiled_eq_original
    (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (P : Prover) (H : Bytes → State) :
    wordsFromRun decoder (eval H (experiment
      (compiled decoder d (wordsFromRun decoder) P) (verifier decoder d))) =
    wordsFromRun decoder (eval H (experiment P (verifier decoder d))) := by
  let original := eval H (experiment P (verifier decoder d))
  let annotated := eval H (experiment
    (compiled decoder d (wordsFromRun decoder) P) (verifier decoder d))
  have hpub : annotated.2.1.1 = original.2.1.1 := by
    dsimp only [annotated, original]
    rw [compiled_experiment_eval]
  have hproof : annotated.2.1.2 =
      RawCutTranscriptRun.proof (wordsFromRun decoder original) original.2.1.2 := by
    dsimp only [annotated, original]
    rw [compiled_experiment_eval]
  have frames (row : Nat) (hrow : row < 33) :
      frameFromView decoder annotated row = frameFromView decoder original row := by
    rw [frameFromView_eq decoder d
      (compiled decoder d (wordsFromRun decoder) P) H row (by omega),
      frameFromView_eq decoder d P H row (by omega)]
    change frame decoder H annotated.2.1.1 annotated.2.1.2 row =
      frame decoder H original.2.1.1 original.2.1.2 row
    rw [hpub, hproof]
    exact congrArg (fun s => (firstCell s).getD [])
      (RawCutTranscriptRun.chain_eq decoder (wordsFromRun decoder original)
        H original.2.1.1 original.2.1.2 row)
  have cuts (row : Nat) (hrow : row < 33) :
      BinRawByteCutRecovery.cut annotated.1 (frameFromView decoder original row) =
      BinRawByteCutRecovery.cut original.1 (frameFromView decoder original row) := by
    have hf : Read original.1 (frameFromView decoder original row) := by
      rw [frameFromView_eq decoder d P H row (by omega)]
      exact frame_read decoder d P H row hrow
    exact commitment_cut_eq decoder d (wordsFromRun decoder) P H _ hf
  change wordsFromRun decoder annotated = wordsFromRun decoder original
  unfold wordsFromRun BinCompiledRunWordStability.wordsFromRun
  rw [frames 0 (by decide), frames 2 (by decide), frames 30 (by decide)]
  unfold BinCanonicalCutWords.wordsFromRawCuts
    BinCanonicalCutWords.rawC1Map BinCanonicalCutWords.rawC2Map
    BinCanonicalCutWords.rawFoldedMap
  dsimp only
  rw [cuts 0 (by decide), cuts 2 (by decide), cuts 30 (by decide)]

/-- The metadata builder retained by the actual generic compiler is exactly
this binary recovery function, so the same equality identifies its output. -/
theorem wordsFromRun_compiled_eq_retainedBuildWords
    (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (P : Prover) (H : Bytes → State) :
    wordsFromRun decoder (eval H (experiment
      (compiled decoder d (wordsFromRun decoder) P) (verifier decoder d))) =
    (wordsFromRun decoder) (eval H (experiment P (verifier decoder d))) :=
  wordsFromRun_compiled_eq_original decoder d P H

#print axioms wordsFromRun_compiled_eq_original
#print axioms wordsFromRun_compiled_eq_retainedBuildWords
end AspisR1.OraclePortWords
end
