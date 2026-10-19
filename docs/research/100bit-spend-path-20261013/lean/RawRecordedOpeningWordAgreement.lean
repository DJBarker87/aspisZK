import RawCutWordsFromRunExecutable
import CanonicalCutSemanticRead
import RawCutTranscriptRun

/-! The executable recorded-log words are the same words read by the metadata-
enriched literal transcript. The equality needed by the executable candidate
extractor is derived from the existing opening-reader theorem, rather than
postulated as a recovered-word correspondence premise. Source opening
acceptance, semantic checks and no-hit conditions remain separate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRecordedOpeningWordAgreement
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RawCutWordsFromRunExecutable CanonicalCutEnrichedTranscript

/-- Successful parsing is preserved under recovered-word metadata enrichment;
the resulting view reads exactly the executable caller's 29 received words. -/
theorem enriched_read_agrees (run : RawCutProverCompiler.RunView)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View) (hread : LiteralOpeningView.read rs = some v) :
    ∃ v', LiteralOpeningView.read (enrichRounds (wordsFromRun run) rs) = some v' ∧
      initialWordsFromRun run = LiteralTypedWords.word ExactBaseProjection.embed
        LiteralSemanticView.eK v'.c1 v'.c2 ∧
      v'.word = initialWordsFromRun run ∧
      v'.challenge25 = v.challenge25 ∧ v'.challenge26 = v.challenge26 ∧
      v'.semantic.map Prod.snd = v.semantic.map Prod.snd ∧
      v'.functionals = v.functionals ∧ v'.baseFunctional = v.baseFunctional := by
  obtain ⟨v', hr, hc1, hc2, hw, hz0, hz1, hs, hf, hb⟩ :=
    CanonicalCutSemanticRead.opening_read_enriched_success (wordsFromRun run) rs v hread
  refine ⟨v', hr, ?_, ?_, hz0, hz1, hs, hf, hb⟩
  · rw [hc1, hc2]
    rfl
  · exact hw

/-- The same agreement holds for the actual literal protocol transcript of
the metadata-enriched proof, using the existing transcript-equivalence theorem. -/
theorem transcript_read_agrees (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n : Nat) (run : RawCutProverCompiler.RunView)
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds = some v) :
    ∃ v', LiteralOpeningView.read
        ((LiteralByteProtocol.protocol decoder).transcript H pub
          (RawCutTranscriptRun.proof (wordsFromRun run) pf) n).rounds = some v' ∧
      initialWordsFromRun run = LiteralTypedWords.word ExactBaseProjection.embed
        LiteralSemanticView.eK v'.c1 v'.c2 ∧
      v'.word = initialWordsFromRun run ∧
      v'.challenge25 = v.challenge25 ∧ v'.challenge26 = v.challenge26 ∧
      v'.semantic.map Prod.snd = v.semantic.map Prod.snd ∧
      v'.functionals = v.functionals ∧ v'.baseFunctional = v.baseFunctional := by
  rw [RawCutTranscriptRun.transcript_eq]
  exact enriched_read_agrees run
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds v hread

#print axioms enriched_read_agrees
#print axioms transcript_read_agrees
end AspisR1.RawRecordedOpeningWordAgreement
end
