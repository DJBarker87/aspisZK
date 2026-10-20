import BinCompiledRunWordStability
import LiteralTableWordChoiceBin
import RWireRawFullPublicRun
import RWireRawCompiledTranscript
import RWireRawCompiledDecoderCompletion

/-! A public-free, table-only decoder completes all 33 actual compiled
protocol rows. Public statement and commitment words are recovered from the
current address/table, with source-format and collision premises explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawAdaptiveCompiledCompletion
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralDecoderEnrichment
open CanonicalCutEnrichedTranscript (Words wordsFromMaps enrichPrefix enrichMessage)
open BinCanonicalCutWords

theorem actual_compiled_transcript
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
    (htag : (eval H (RawCutProverCompiler.experiment prover
      (RawCutProverCompiler.verifier decoder d))).2.1.1.tag = 2)
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
      let compiled := eval H (RawCutProverCompiler.experiment
        (RawCutProverCompiler.compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) prover)
        (RawCutProverCompiler.verifier decoder d))
      let out := RWireRawCompiledTranscript.output decoder d prover H
      let raw := RawCutWordsFromView.frame decoder H out.1 out.2 n
      ∃ own pend g,
        RawAdaptiveLiteralDecoder.decode RWireRawFullPublicSelection.select LiteralTableWordChoiceBin.choose raw
          (tableBefore emptyTable compiled.1 raw) = some (own, pend, g) ∧
        bfollow g (traceFrom compiled.1 raw) own pend (tableBefore emptyTable compiled.1 raw) =
          some ((LiteralByteProtocol.protocol decoder).transcript H out.1 out.2 n,
            (LiteralByteProtocol.protocol decoder).msg out.2 n,
            (LiteralByteProtocol.protocol decoder).chal H out.1 out.2 n) := by
  intro n hn
  let original := RWireRawCompiledTranscript.original decoder d prover H
  let out := RWireRawCompiledTranscript.output decoder d prover H
  let compiled := eval H (RawCutProverCompiler.experiment
    (RawCutProverCompiler.compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) prover)
    (RawCutProverCompiler.verifier decoder d))
  let raw := RawCutWordsFromView.frame decoder H out.1 out.2 n
  have hs : RWireRawFullPublicSelection.select raw (tableBefore emptyTable compiled.1 raw) = some out.1 := by
    dsimp only [raw,out,compiled]
    rw [RWireRawCompiledTranscript.frame,RWireRawCompiledTranscript.output_eq]
    rw [RawCutProverCompiler.compiled_experiment_eval]
    have hread := RawCutWordsFromView.frame_read decoder d prover H n hn
    dsimp only [RWireRawCompiledTranscript.original] at hread ⊢
    rw [TraceAppend.tableBefore_append _ _ _ _ hread]
    exact RWireRawFullPublicRun.select_actual_run decoder d prover H Q hQ hout hvalid htag n hn
  have hb := RWireRawCompiledDecoderCompletion.actual_compiled_transcript decoder d prover H
    Q hQ hout hvalid r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30 n hn
  rcases hb with ⟨own,pend,g,hd,hf⟩
  refine ⟨own,pend,g,?_,hf⟩
  rw [RawAdaptiveLiteralDecoder.decode_of_public _ _ _ _ _ hs]
  exact hd

#print axioms actual_compiled_transcript

end AspisR1.RWireRawAdaptiveCompiledCompletion
end
