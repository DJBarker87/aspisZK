import BinCompiledRunWordStability
import LiteralTableWordChoiceBin
import RWireRawFullPublicSelection
import RWireRawLiteralRecordedDecoder

/-! Recover the public statement from the actual adaptive prover experiment
for all 33 rows, and compose that recovery with the concrete table-derived
decoder. No statement is supplied as an input to the decoder. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawFullPublicRun
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralDecoderEnrichment
open CanonicalCutEnrichedTranscript (Words wordsFromMaps enrichPrefix enrichMessage)
open BinCanonicalCutWords

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

theorem frame_firstCell (decoder : LiteralByteProtocol.Decoder)
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

theorem select_actual_run
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) (Q : Nat)
    (hQ : firstReads emptyTable
      (eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred Q)
      emptyTable (eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))).1)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i
      ((eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))).2.1.2 i))
    (htag : (eval H (RawCutProverCompiler.experiment prover
      (RawCutProverCompiler.verifier decoder d))).2.1.1.tag = 2)
    (n : Nat) (hn : n < 33) :
    let run := eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))
    let raw := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
    RWireRawFullPublicSelection.select raw (tableBefore emptyTable run.1 raw) = some run.2.1.1 := by
  let run : RawCutProverCompiler.RunView := eval H
    (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))
  let pub := run.2.1.1
  let pf := run.2.1.2
  let prior := (eval H prover).1
  let draw := RawCutTranscriptRun.decisionOnBytes d
  have htr : RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior = run.1 := by
    dsimp [RWireLiteralLegacyDecoderCompletion.rawTrace, run, pub, pf, prior, draw,
      RawCutTranscriptRun.decisionOnBytes]
    rw [RawCutProverCompiler.experiment_eval]
    rfl
  have hQ' : firstReads emptyTable
      (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) ≤ Q := by
    rw [htr]
    exact hQ
  have hout' : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred Q)
      emptyTable (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) := by
    rw [htr]
    exact hout
  have hs := RWireRawFullPublicSelection.at_first_cell decoder draw H pub pf hvalid htag
    prior (FS.eval_consistent H prover) Q hQ' hout' n hn
    (RawCutWordsFromView.frame decoder H pub pf n) (frame_firstCell decoder H pub pf n)
  rw [htr] at hs
  exact hs

theorem adaptive_run_decodes_and_follows
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
      let run := eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))
      let pub := run.2.1.1
      let pf := run.2.1.2
      let raw := RawCutWordsFromView.frame decoder H pub pf n
      ∃ own pend g,
        RawAdaptiveLiteralDecoder.decode RWireRawFullPublicSelection.select LiteralTableWordChoiceBin.choose raw
          (tableBefore emptyTable run.1 raw) = some (own, pend, g) ∧
        bfollow g (traceFrom run.1 raw) own pend (tableBefore emptyTable run.1 raw) =
          some (enrichPrefix (BinCompiledRunWordStability.wordsFromRun decoder run)
              ((LiteralByteProtocol.protocol decoder).transcript H pub pf n),
            enrichMessage (BinCompiledRunWordStability.wordsFromRun decoder run) (pf n),
            (LiteralByteProtocol.protocol decoder).chal H pub pf n) := by
  intro n hn
  have hs := select_actual_run decoder d prover H Q hQ hout hvalid htag n hn
  have hb := RWireRawLiteralRecordedDecoder.actual_run_decodes_and_follows decoder d prover H
    Q hQ hout hvalid r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30 n (by omega)
  rcases hb with ⟨own,pend,g,hd,hf⟩
  refine ⟨own,pend,g,?_,hf⟩
  rw [RawAdaptiveLiteralDecoder.decode_of_public _ _ _ _ _ hs]
  exact hd

#print axioms select_actual_run
#print axioms adaptive_run_decodes_and_follows
#print axioms firstCell_map
#print axioms frame_firstCell
end AspisR1.RWireRawFullPublicRun
end
