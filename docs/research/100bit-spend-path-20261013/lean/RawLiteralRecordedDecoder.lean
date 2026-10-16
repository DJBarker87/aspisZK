import RawLiteralDecoderRestore
import LiteralTableChoiceWords
import RawCutWordsFromView

/-! The table-only word choice completes the actual recorded byte-protocol
run's literal decoder, row by row. The only source-format premises are the
three concrete commitment messages and their strict payload parses. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawLiteralRecordedDecoder

open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

private theorem frame_firstCell (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n : Nat) :
    firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) =
      some (RawCutWordsFromView.frame decoder H pub pf n) := by
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf n
  have hbounded : firstCell (LiteralTranscript.samp n P
      ((LiteralByteProtocol.protocol decoder).msg pf n)) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  have hne : firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) ≠ none := by
    change firstCell (ProgramSamplerMap.map Addr.toBytes _) ≠ none
    rw [firstCell_map]
    simpa [P] using hbounded
  unfold RawCutWordsFromView.frame
  cases h : firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) with
  | none => exact False.elim (hne h)
  | some a => simp [h]

/-- For each actual verifier row, the concrete commitment-cut word choice
feeds the existing raw-decoder completion theorem without a supplied word
agreement premise. -/
theorem actual_run_decodes_and_follows
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State)
    (Q : Nat)
    (hQ : firstReads emptyTable
      (eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv RawByteCollisionTargets.pred Q)
      emptyTable (eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))).1)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i
      ((eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))).2.1.2 i))
    (r1 : State) (w1 : LiteralTranscript.C1Word)
    (b2 : LiteralTranscript.BytesMessage) (w2 : LiteralTranscript.C2Word) (r2 : State)
    (b30 : LiteralTranscript.BytesMessage) (w30 : LiteralTranscript.VWord)
    (v30 : OpeningRecordCodec.Payload .second)
    (h0 : (eval H (RawCutProverCompiler.experiment prover
      (RawCutProverCompiler.verifier decoder d))).2.1.2 0 = .initial r1 w1)
    (h2 : (eval H (RawCutProverCompiler.experiment prover
      (RawCutProverCompiler.verifier decoder d))).2.1.2 2 = .c2 b2 w2)
    (h30 : (eval H (RawCutProverCompiler.experiment prover
      (RawCutProverCompiler.verifier decoder d))).2.1.2 30 = .second b30 w30)
    (hp2 : SemanticRecordCodec.decode ⟨2, by decide⟩ b2.val =
      some ⟨.c2Root r2, by rfl⟩)
    (hp30 : OpeningRecordCodec.decode .second b30.val = some v30) :
    ∀ n, n < 33 →
      let run := eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))
      let pub := run.2.1.1
      let pf := run.2.1.2
      let raw := RawCutWordsFromView.frame decoder H pub pf n
      ∃ own pend g,
        RawLiteralDecoderDensity.decode LiteralTableWordChoice.choose pub raw
          (tableBefore emptyTable run.1 raw) = some (own, pend, g) ∧
        bfollow g (traceFrom run.1 raw) own pend (tableBefore emptyTable run.1 raw) =
          some (enrichPrefix (RawCutWordsFromView.buildWords decoder run)
              ((LiteralByteProtocol.protocol decoder).transcript H pub pf n),
            enrichMessage (RawCutWordsFromView.buildWords decoder run) (pf n),
            (LiteralByteProtocol.protocol decoder).chal H pub pf n) := by
  intro n hn
  let run : RawCutProverCompiler.RunView := eval H
    (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))
  let pub := run.2.1.1
  let pf := run.2.1.2
  let prior := (eval H prover).1
  let draw := RawCutTranscriptRun.decisionOnBytes d
  let raw := RawCutWordsFromView.frame decoder H pub pf n
  have htr : LiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior = run.1 := by
    dsimp [LiteralLegacyDecoderCompletion.rawTrace, run, pub, pf, prior, draw,
      RawCutTranscriptRun.decisionOnBytes]
    rw [RawCutProverCompiler.experiment_eval]
    rfl
  have hQ' : firstReads emptyTable
      (LiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) ≤ Q := by
    rw [htr]
    exact hQ
  have hout' : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv RawByteCollisionTargets.pred Q)
      emptyTable (LiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) := by
    rw [htr]
    exact hout
  have hprior : ∀ q ∈ prior, q.2 = H q.1 := FS.eval_consistent H prover
  have hfirst : firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) = some raw := by
    dsimp only [raw]
    exact frame_firstCell decoder H pub pf n
  have hcomponents := LiteralTableChoiceWords.constructed_components decoder d prover H run rfl
    SelectedTranscriptParams.params.iv Q hQ hout hvalid n hn r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30
  have hwords :
      let tr := LiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior
      let T := tableBefore emptyTable tr raw
      let w := LiteralTableWordChoice.choose raw T
        (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n))
        (LiteralTranscript.erase (pf n))
      w.c1 = (RawCutWordsFromView.buildWords decoder run).c1 ∧
        (2 ≤ n → w.c2 = (RawCutWordsFromView.buildWords decoder run).c2) ∧
        (30 ≤ n → w.final = (RawCutWordsFromView.buildWords decoder run).final) := by
    dsimp only [LiteralTableChoiceWords.atRun] at hcomponents
    rw [← htr] at hcomponents
    simpa [raw] using hcomponents
  have hrest := RawLiteralDecoderRestore.decodes_and_follows decoder draw H pub pf hvalid
    prior hprior Q hQ' hout' n hn raw hfirst LiteralTableWordChoice.choose
    (RawCutWordsFromView.buildWords decoder run) hwords
  simpa only [run, pub, pf, raw, htr] using hrest

#print axioms actual_run_decodes_and_follows
end AspisR1.RawLiteralRecordedDecoder
end
