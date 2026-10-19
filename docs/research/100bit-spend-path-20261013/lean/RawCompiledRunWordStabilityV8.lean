import RawCutWordsFromRunExecutable

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCompiledRunWordStability

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.RawCutWordsFromView
open AspisR1.RawCommitmentFrameReplay
open AspisR1.RawCommitmentFrameReplayCorrect
open AspisR1.RawCutRecordedWordsExecutable
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.LiteralTranscript

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

attribute [local irreducible] RawCutWordsFromView.buildWords

private theorem wordsFromRawCuts_eq_of_same_cuts
    (tr₁ tr₂ : List (Bytes × State))
    (f0 f2 f30 : Bytes) (r0 r2 r30 : State)
    (h0 : RawByteCutRecovery.cut tr₁ f0 = RawByteCutRecovery.cut tr₂ f0)
    (h2 : RawByteCutRecovery.cut tr₁ f2 = RawByteCutRecovery.cut tr₂ f2)
    (h30 : RawByteCutRecovery.cut tr₁ f30 = RawByteCutRecovery.cut tr₂ f30) :
    wordsFromRawCuts tr₁ f0 f2 f30 r0 r2 r30 =
      wordsFromRawCuts tr₂ f0 f2 f30 r0 r2 r30 := by
  unfold wordsFromRawCuts wordsFromMaps rawC1Map rawC2Map rawFoldedMap
  rw [h0, h2, h30]

/-- Recovered metadata is stable when the compiler records the original run,
then appends the verifier replay with metadata-enriched messages. The only
validity assumptions are the exact prefix conditions needed by frame replay;
the log-cut equality itself is supplied by `commitment_cut_eq`. -/
theorem wordsFromRun_compiled_eq_original
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State)
    (hvalidOriginal : ∀ j, j ≤ 30 → LiteralTranscript.valid j
      ((eval H (experiment P (verifier decoder d))).2.1.2 j))
    (hvalidCompiled : ∀ j, j ≤ 30 → LiteralTranscript.valid j
      ((eval H (experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))).2.1.2 j)) :
    RawCutWordsFromRunExecutable.wordsFromRun
      (eval H (experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))) =
    RawCutWordsFromRunExecutable.wordsFromRun
      (eval H (experiment P (verifier decoder d))) := by
  let original := eval H (experiment P (verifier decoder d))
  let annotated := eval H (experiment
    (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
    (verifier decoder d))
  have hpub : annotated.2.1.1 = original.2.1.1 := by
    dsimp only [annotated, original]
    rw [compiled_experiment_eval]
  have hproof : annotated.2.1.2 =
      RawCutTranscriptRun.proof (RawCutWordsFromView.buildWords decoder original)
        original.2.1.2 := by
    dsimp only [annotated, original]
    rw [compiled_experiment_eval]
  have hca := frameFromView_commitments_eq decoder annotated
    (fun j hj => hvalidCompiled j hj)
  have hoa := frameFromView_commitments_eq decoder original
    (fun j hj => hvalidOriginal j hj)

  let f0 := RawCutWordsFromView.frame decoder H original.2.1.1 original.2.1.2 0
  let f2 := RawCutWordsFromView.frame decoder H original.2.1.1 original.2.1.2 2
  let f30 := RawCutWordsFromView.frame decoder H original.2.1.1 original.2.1.2 30
  have hcut0 := commitment_cut_eq decoder d
    (RawCutWordsFromView.buildWords decoder) P H f0
    (by
      simpa only [f0, original] using RawCutWordsFromView.frame_read decoder d P H 0 (by decide))
  have hcut2 := commitment_cut_eq decoder d
    (RawCutWordsFromView.buildWords decoder) P H f2
    (by
      simpa only [f2, original] using RawCutWordsFromView.frame_read decoder d P H 2 (by decide))
  have hcut30 := commitment_cut_eq decoder d
    (RawCutWordsFromView.buildWords decoder) P H f30
    (by
      simpa only [f30, original] using RawCutWordsFromView.frame_read decoder d P H 30 (by decide))
  have hc0 : RawByteCutRecovery.cut annotated.1 f0 =
      RawByteCutRecovery.cut original.1 f0 := by
    simpa only [annotated, original] using hcut0
  have hc2 : RawByteCutRecovery.cut annotated.1 f2 =
      RawByteCutRecovery.cut original.1 f2 := by
    simpa only [annotated, original] using hcut2
  have hc30 : RawByteCutRecovery.cut annotated.1 f30 =
      RawByteCutRecovery.cut original.1 f30 := by
    simpa only [annotated, original] using hcut30
  have hf0 : RawCommitmentFrameReplay.frameFromView annotated 0 = f0 := by
    calc
      _ = RawCutWordsFromView.frameFromView decoder annotated 0 := hca.1
      _ = RawCutWordsFromView.frame decoder H annotated.2.1.1 annotated.2.1.2 0 := by
        exact RawCutWordsFromView.frameFromView_eq decoder d
          (compiled decoder d (RawCutWordsFromView.buildWords decoder) P) H 0 (by decide)
      _ = f0 := by
        rw [hpub, hproof]
        exact congrArg (fun s => (firstCell s).getD [])
          (RawCutTranscriptRun.chain_eq decoder (RawCutWordsFromView.buildWords decoder original)
            H original.2.1.1 original.2.1.2 0)
  have hf2 : RawCommitmentFrameReplay.frameFromView annotated 2 = f2 := by
    calc
      _ = RawCutWordsFromView.frameFromView decoder annotated 2 := hca.2.1
      _ = RawCutWordsFromView.frame decoder H annotated.2.1.1 annotated.2.1.2 2 := by
        exact RawCutWordsFromView.frameFromView_eq decoder d
          (compiled decoder d (RawCutWordsFromView.buildWords decoder) P) H 2 (by decide)
      _ = f2 := by
        rw [hpub, hproof]
        exact congrArg (fun s => (firstCell s).getD [])
          (RawCutTranscriptRun.chain_eq decoder (RawCutWordsFromView.buildWords decoder original)
            H original.2.1.1 original.2.1.2 2)
  have hf30 : RawCommitmentFrameReplay.frameFromView annotated 30 = f30 := by
    calc
      _ = RawCutWordsFromView.frameFromView decoder annotated 30 := hca.2.2
      _ = RawCutWordsFromView.frame decoder H annotated.2.1.1 annotated.2.1.2 30 := by
        exact RawCutWordsFromView.frameFromView_eq decoder d
          (compiled decoder d (RawCutWordsFromView.buildWords decoder) P) H 30 (by decide)
      _ = f30 := by
        rw [hpub, hproof]
        exact congrArg (fun s => (firstCell s).getD [])
          (RawCutTranscriptRun.chain_eq decoder (RawCutWordsFromView.buildWords decoder original)
            H original.2.1.1 original.2.1.2 30)
  have ho0 : RawCommitmentFrameReplay.frameFromView original 0 = f0 := by
    calc
      _ = RawCutWordsFromView.frameFromView decoder original 0 := hoa.1
      _ = RawCutWordsFromView.frame decoder H original.2.1.1 original.2.1.2 0 :=
        RawCutWordsFromView.frameFromView_eq decoder d P H 0 (by decide)
  have ho2 : RawCommitmentFrameReplay.frameFromView original 2 = f2 := by
    calc
      _ = RawCutWordsFromView.frameFromView decoder original 2 := hoa.2.1
      _ = RawCutWordsFromView.frame decoder H original.2.1.1 original.2.1.2 2 :=
        RawCutWordsFromView.frameFromView_eq decoder d P H 2 (by decide)
  have ho30 : RawCommitmentFrameReplay.frameFromView original 30 = f30 := by
    calc
      _ = RawCutWordsFromView.frameFromView decoder original 30 := hoa.2.2
      _ = RawCutWordsFromView.frame decoder H original.2.1.1 original.2.1.2 30 :=
        RawCutWordsFromView.frameFromView_eq decoder d P H 30 (by decide)
  change RawCutRecordedWordsExecutable.wordsFromRecordedLogExec annotated.1
      (RawCommitmentFrameReplay.frameFromView annotated 0)
      (RawCommitmentFrameReplay.frameFromView annotated 2)
      (RawCommitmentFrameReplay.frameFromView annotated 30) =
    RawCutRecordedWordsExecutable.wordsFromRecordedLogExec original.1
      (RawCommitmentFrameReplay.frameFromView original 0)
      (RawCommitmentFrameReplay.frameFromView original 2)
      (RawCommitmentFrameReplay.frameFromView original 30)
  rw [hf0, hf2, hf30, ho0, ho2, ho30]
  rw [wordsFromRecordedLogExec_eq_wordsFromRawCuts,
    wordsFromRecordedLogExec_eq_wordsFromRawCuts]
  exact wordsFromRawCuts_eq_of_same_cuts annotated.1 original.1 f0 f2 f30
    (rootFromExec 8 f0) (rootFromExec 8 f2) (rootFromExec 9 f30) hc0 hc2 hc30


/-- If the original prefix is valid as well, the compiled run's recovered
words are exactly the retained builder result used to annotate that run. -/
theorem wordsFromRun_compiled_eq_retainedBuildWords
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State)
    (hvalidOriginal : ∀ j, j ≤ 30 → LiteralTranscript.valid j
      ((eval H (experiment P (verifier decoder d))).2.1.2 j))
    (hvalidCompiled : ∀ j, j ≤ 30 → LiteralTranscript.valid j
      ((eval H (experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))).2.1.2 j)) :
    RawCutWordsFromRunExecutable.wordsFromRun
      (eval H (experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))) =
    RawCutWordsFromView.buildWords decoder
      (eval H (experiment P (verifier decoder d))) := by
  calc
    _ = RawCutWordsFromRunExecutable.wordsFromRun
        (eval H (experiment P (verifier decoder d))) :=
      wordsFromRun_compiled_eq_original decoder d P H hvalidOriginal hvalidCompiled
    _ = RawCutWordsFromView.buildWords decoder
        (eval H (experiment P (verifier decoder d))) :=
      wordsFromRun_eq_buildWords decoder _ hvalidOriginal

#print axioms wordsFromRun_compiled_eq_original
#print axioms wordsFromRun_compiled_eq_retainedBuildWords
end AspisR1.RawCompiledRunWordStability
end
