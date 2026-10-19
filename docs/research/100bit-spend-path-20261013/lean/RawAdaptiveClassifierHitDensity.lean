import RawAdaptiveLiteralDecoder
import LiteralBudgetEnvelope

/-! Direct decoded-classifier density and the actual lazy-oracle causal
first-read bound. No doomed/choice-extractor condition is needed, and no
query factor is discarded. Concrete transcript completion is separate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawAdaptiveClassifierHitDensity
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript
open RawLiteralDecoderDensity

attribute [local irreducible] LiteralClassifier.bad

def classifier (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (_T : Table Bytes State) (c : LiteralTranscript.Challenge) : Prop :=
  LiteralClassifier.bad P m c

/-- The raw decoder's existing all-row background law applies to the
classifier event itself, without a failed specification extractor premise. -/
theorem literal_decoded_classifier_le
    (choose : WordChoice) (pub : LiteralTranscript.Public)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : RawLiteralDecoderDensity.decode choose pub a T = some (own, pend, g)) :
    blaw g (fun out => indicator (classifier out.1 out.2.1 T out.2.2)) own pend ≤
      PerAttemptEnvelope.B := by
  unfold RawLiteralDecoderDensity.decode at hd
  cases hc : RawUnifiedDecoder.decode SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T with
  | none => simp [hc] at hd
  | some result =>
    rcases result with ⟨bs, bp, bg⟩
    simp only [hc, Option.map_some] at hd
    have hbound : blaw bg (fun out => indicator
        (classifier (restore (choose a T) out).1
          (restore (choose a T) out).2.1 T (restore (choose a T) out).2.2)) bs bp ≤
        PerAttemptEnvelope.B := by
      refine RawUnifiedDecoder.decoded_bound SelectedTranscriptParams.params
        (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        pub a T bs bp bg hc _ PerAttemptEnvelope.B ?_
      intro i P m hi hround
      subst i
      exact (LiteralDecoderEnrichment.density (choose a T P m) P m hi).trans
        (LiteralBudgetEnvelope.row_le P.round hi)
    cases hd
    rw [BackgroundLawMap.blaw_map]
    exact hbound

/-- Public and commitment-word selection depend only on the input table,
so adaptive statement selection does not introduce a union over statements. -/
theorem adaptive_decoded_classifier_le
    (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice) (words : WordChoice)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : RawAdaptiveLiteralDecoder.decode pubChoice words a T = some (own, pend, g)) :
    blaw g (fun out => indicator (classifier out.1 out.2.1 T out.2.2)) own pend ≤
      PerAttemptEnvelope.B := by
  unfold RawAdaptiveLiteralDecoder.decode at hd
  cases hp : pubChoice a T with
  | none => simp [hp] at hd
  | some pub =>
    simp only [hp, Option.bind_some] at hd
    exact literal_decoded_classifier_le words pub a T own pend g hd

/-- This is the shared-ROM decoded-hit mass bound, with its distinct-first-read
factor Q retained. It is not the fresh 33-round probability statement. -/
theorem shared_decoded_hit_mass_le
    {Pf : Type}
    (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice) (words : WordChoice)
    (exp : Program Bytes State (Pf × Bool)) (Q : Nat)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable (eval H exp).1 ≤ Q) :
    lazyMean exp emptyTable (fun run => indicator
      (hitsChain3 (RawAdaptiveLiteralDecoder.decode pubChoice words)
        classifier emptyTable run.1)) ≤ (Q : ℚ) * PerAttemptEnvelope.B := by
  apply lemmaA3 (RawAdaptiveLiteralDecoder.decode pubChoice words) classifier
    PerAttemptEnvelope.B exp emptyTable Q
  · unfold PerAttemptEnvelope.B
    positivity
  · exact adaptive_decoded_classifier_le pubChoice words
  · apply firstReadsBound_of_traces
    exact hQ

#print axioms literal_decoded_classifier_le
#print axioms adaptive_decoded_classifier_le
#print axioms shared_decoded_hit_mass_le
end AspisR1.RawAdaptiveClassifierHitDensity
end
