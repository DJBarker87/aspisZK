import AspisRec40Frames
import AspisRec40CleanB

/-! Aspis 40-row clean event: `clean40`, R1's `Frozen2StartChargeClean.clean`
for the 40-row experiment at the one-transaction decision `dV_aspis`.

Two named hypotheses, with exactly the shapes stated in
`AspisRec40CleanStatement` / RECORDED-EXPERIMENT-40.md §7.2:
* `hchecks`: `CheckedAcceptance40` at every stored input (the game agent's
  M9; R1's `fibre_checks`). It is stated at `ChargePrefix.prover P`, which is
  R1's `pairProver s P` as a program (R1's `Frozen2StartChargePrefix.fibre_prover`).
* `hfinal`: decoding of rows 33 to 39 on the charged run, under R1's four
  premises of `Frozen2StartChargeCompletion.decodes` (mine, to be discharged).
Everything else is proved here: the full experiment equals the recorded
decision experiment, acceptance and output transport, the constructor
schedule and `Format` from `AspisChecks` fields, the public tag from
`admitted_aspis`/`accepted_guardS`, the word alignment, and the assembly. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanWords
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open RawCutProverCompiler (experiment)
open CanonicalCutEnrichedTranscript (Words enrichMessage)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

/-! ## Word alignment -/

private theorem proof_idempotent (w : Words) (pf : LiteralProtocol.Proof) :
    RawCutTranscriptRun.proof w (RawCutTranscriptRun.proof w pf) =
      RawCutTranscriptRun.proof w pf := by
  funext i
  cases h : pf i <;> simp [RawCutTranscriptRun.proof, enrichMessage, h]

/-- Copy of `OraclePortCleanModel.extractor_word_alignment`, with `AspisChecks`. -/
theorem extractor_word_alignment (D : LiteralByteProtocol.Decoder)
    (d : OracleDecisionFeasibilityCore.Decision) (P : RawCutProverCompiler.Prover)
    (H : Bytes → State)
    (checks : let run := eval H (AspisRec40.Decision.recorded D d P)
      AspisAcceptance.AspisChecks AspisOneTx.decodePairS run.2.1.1
        ((pr D).transcript H run.2.1.1 run.2.1.2 40).rounds) :
    let orig := eval H (experiment P (AspisRec40.Decision.verifier D d))
    let run := eval H (AspisRec40.Decision.recorded D d P)
    RawCutWordsFromRunExecutableBin.wordsFromRun run =
        BinCompiledRunWordStability.wordsFromRun D orig ∧
      RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun run) run.2.1.2 =
        run.2.1.2 := by
  intro orig run
  have hpf : run.2.1.2 = RawCutTranscriptRun.proof
      (BinCompiledRunWordStability.wordsFromRun D orig) orig.2.1.2 := by
    change (eval H (AspisRec40.Decision.annotated D d (BinCompiledRunWordStability.wordsFromRun D) P)).2.1.2 = _
    rw [AspisRec40.Decision.annotated, AspisRec40.Decision.compiled_experiment_eval]
  have hvalidRun : RawCutWordsFromRunExecutableBin.ValidPrefix run := by
    intro j hj
    exact AspisRec40.CleanB.valid_of_checks D H run.2.1.1 run.2.1.2 checks j (by omega)
  have hw1 := RawCutWordsFromRunExecutableBin.wordsFromRun_eq_buildWords D run hvalidRun
  have hw2 : BinCompiledRunWordStability.wordsFromRun D run =
      BinCompiledRunWordStability.wordsFromRun D orig :=
    AspisRec40.Frames.wordsFromRun_compiled_eq_original D d P H
  have hwords := hw1.trans hw2
  refine ⟨hwords, ?_⟩
  rw [hwords, hpf]
  exact proof_idempotent _ _

#print axioms extractor_word_alignment

end AspisRec40.CleanWords
end
