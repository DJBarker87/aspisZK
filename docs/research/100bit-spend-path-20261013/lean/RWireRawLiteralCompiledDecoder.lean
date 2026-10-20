import BinCompiledRunWordStability
import LiteralTableWordChoiceBin
import RWireRawLiteralRecordedDecoder
import RawCutProverCompiler
import R1TraceAppend
import R1FollowAppend

/-! The compiler appends a repeated verifier trace. At a frame already read
before that suffix, the table stays fixed and the completed follow extends. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawLiteralCompiledDecoder

open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralDecoderEnrichment
open CanonicalCutEnrichedTranscript (Words wordsFromMaps enrichPrefix enrichMessage)
open BinCanonicalCutWords

theorem compiled_run_decodes_and_follows
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State)
    (Q : Nat)
    (hQ : firstReads emptyTable
      (eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred Q)
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
      let original := eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))
      let compiled := eval H (RawCutProverCompiler.experiment
        (RawCutProverCompiler.compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) prover)
        (RawCutProverCompiler.verifier decoder d))
      let pub := original.2.1.1
      let pf := original.2.1.2
      let raw := RawCutWordsFromView.frame decoder H pub pf n
      ∃ own pend g,
        RawLiteralDecoderDensity.decode LiteralTableWordChoiceBin.choose pub raw
          (tableBefore emptyTable compiled.1 raw) = some (own, pend, g) ∧
        bfollow g (traceFrom compiled.1 raw) own pend (tableBefore emptyTable compiled.1 raw) =
          some (enrichPrefix (BinCompiledRunWordStability.wordsFromRun decoder original)
              ((LiteralByteProtocol.protocol decoder).transcript H pub pf n),
            enrichMessage (BinCompiledRunWordStability.wordsFromRun decoder original) (pf n),
            (LiteralByteProtocol.protocol decoder).chal H pub pf n) := by
  intro n hn
  let original : RawCutProverCompiler.RunView := eval H
    (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))
  let compiled : RawCutProverCompiler.RunView := eval H
    (RawCutProverCompiler.experiment
      (RawCutProverCompiler.compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) prover)
      (RawCutProverCompiler.verifier decoder d))
  have htrace0 := congrArg (fun v : RawCutProverCompiler.RunView => v.1)
    (RawCutProverCompiler.compiled_experiment_eval decoder d
      (BinCompiledRunWordStability.wordsFromRun decoder) prover H)
  let tail := (eval H (RawCutProverCompiler.verifier decoder d
    original.2.1.1 original.2.1.2)).1
  have hsplit : compiled.1 = original.1 ++ tail := by
    dsimp only [compiled, original, tail, RawCutProverCompiler.experiment,
      RawCutProverCompiler.compiled] at htrace0 ⊢
    exact htrace0
  have hbase := RWireRawLiteralRecordedDecoder.actual_run_decodes_and_follows decoder d prover H
    Q hQ hout hvalid r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30 n hn
  rcases hbase with ⟨own, pend, g, hdecode, hfollow⟩
  let raw := RawCutWordsFromView.frame decoder H original.2.1.1 original.2.1.2 n
  have hread : Read original.1 raw := by
    simpa [raw, original] using
      RawCutWordsFromView.frame_read decoder d prover H n hn
  have hmem : raw ∈ original.1.map Prod.fst := hread
  have htable := TraceAppend.tableBefore_append emptyTable original.1 tail raw hmem
  have htraceFrom := TraceAppend.traceFrom_append original.1 tail raw hmem
  have hdecodeCompiled : RawLiteralDecoderDensity.decode LiteralTableWordChoiceBin.choose
      original.2.1.1 raw (tableBefore emptyTable compiled.1 raw) = some (own, pend, g) := by
    rw [hsplit, htable]
    exact hdecode
  have hfollowCompiled : bfollow g (traceFrom compiled.1 raw) own pend
      (tableBefore emptyTable compiled.1 raw) =
      some (enrichPrefix (BinCompiledRunWordStability.wordsFromRun decoder original)
          ((LiteralByteProtocol.protocol decoder).transcript H original.2.1.1 original.2.1.2 n),
        enrichMessage (BinCompiledRunWordStability.wordsFromRun decoder original) (original.2.1.2 n),
        (LiteralByteProtocol.protocol decoder).chal H original.2.1.1 original.2.1.2 n) := by
    rw [hsplit, htraceFrom, htable]
    exact FollowAppend.bfollow_append_of_some g (traceFrom original.1 raw) tail own pend
      (tableBefore emptyTable original.1 raw) _ hfollow
  exact ⟨own, pend, g, by simpa only [original, compiled, raw] using hdecodeCompiled,
    by simpa only [original, compiled, raw] using hfollowCompiled⟩

#print axioms compiled_run_decodes_and_follows

end AspisR1.RWireRawLiteralCompiledDecoder
end
