import R1UnifiedDecoder
import R1UnifiedInitialLaw
import R1UnifiedSemanticLaw
import R1UnifiedReseedLaw
import R1UnifiedOpeningLaw
import R1UnifiedQueryLaw
import R1JointUnifiedBound
import R1DecoderStateList

/-! Dispatch a uniform fixed-round sampler bound through the row-indexed
unified decoder. This composes existing component laws without supplying a
numeric bound or a source/security premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedDecoderBound

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem component_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (hn : n < 33)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hcomponent : UnifiedDecoder.component p hD pub n a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ (i : Nat) (P : UnifiedSampler.Prefix M Cv L) (m : Message M),
      i < 33 → P.rounds.length = i →
        independentMean (UnifiedSampler.samp p hD i P m).toProgram
          (fun w => obs (P, m, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  by_cases h0 : n = 0
  · subst n
    rw [UnifiedDecoder.component_initial] at hcomponent
    obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
      DecoderStateList.lift_sound (UnifiedInitialDecoder.decode p hD pub) pub a T
        own pend g hcomponent
    have hfixed₀ : ∀ c1,
        PublicInitParse.parse pub.pubBytes a = some c1 →
          independentMean
            (UnifiedSampler.samp p hD 0 (emptyPrefix pub) (.initial c1)).toProgram
            (fun w => obs (emptyPrefix pub, .initial c1, w.2)) ≤ B := by
      intro c1 hc1
      exact hfixed 0 (emptyPrefix pub) (.initial c1) (by omega) (by rfl)
    have hbound := UnifiedInitialLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
      hdecode obs B hfixed₀
    cases heq
    rw [DecoderStateList.lifted_law]
    exact hbound
  · by_cases hsem : n < 26
    · have hnlo : 0 < n := by omega
      rw [UnifiedDecoder.component_semantic p hD pub n hnlo hsem] at hcomponent
      obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
        DecoderStateList.lift_sound (UnifiedSemanticDecoder.decode p pub) pub a T
          own pend g hcomponent
      have hfixed_sem : ∀ ctx,
          UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx →
          0 < ctx.records.length → ctx.records.length < 26 →
          ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
            independentMean
              (UnifiedSampler.samp p hD ctx.records.length
                (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
              (fun w => obs
                (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)) ≤ B := by
        intro ctx hp hlo hhi as has
        have hround :
            (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = ctx.records.length := by
          simp [UnifiedSemanticLaw.mkPrefix, TranscriptView.ordinary_length,
            PrefixRecordLength.fromAnswers_length]
        exact hfixed ctx.records.length
          (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)
          (by omega) hround
      have hbound := UnifiedSemanticLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
        hdecode obs B hfixed_sem
      cases heq
      rw [DecoderStateList.lifted_law]
      exact hbound
    · by_cases h26 : n = 26
      · subst n
        rw [UnifiedDecoder.component_reseed] at hcomponent
        obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
          DecoderStateList.lift_sound (UnifiedReseedDecoder.decode p pub) pub a T
            own pend g hcomponent
        have hfixed_reseed : ∀ ctx,
            UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx →
            ctx.records.length = 26 →
            ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
              independentMean
                (UnifiedSampler.samp p hD 26
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
                (fun w => obs
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)) ≤ B := by
          intro ctx hp hlen as has
          have hround :
              (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = ctx.records.length := by
            simp [UnifiedSemanticLaw.mkPrefix, TranscriptView.ordinary_length,
              PrefixRecordLength.fromAnswers_length]
          exact hfixed 26 (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
            (.payload ctx.message) (by decide) (by omega)
        have hbound := UnifiedReseedLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
          hdecode obs B hfixed_reseed
        cases heq
        rw [DecoderStateList.lifted_law]
        exact hbound
      · by_cases h31 : n = 31
        · subst n
          rw [UnifiedDecoder.component_query] at hcomponent
          exact UnifiedQueryLaw.decoded_bound p hD pub a T own pend g hcomponent obs B
            (by
              intro ctx hp hlen as has
              have hround :
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = 31 := by
                have h := PrefixRecordLength.fromAnswers_length p T 0 ctx.records as
                change (TranscriptView.ordinary ctx.c1
                  (PrefixAnswers.fromAnswers p T 0 ctx.records
                    (as.take (PrefixAnswers.missing p T ctx.records).length))).length = 31
                rw [TranscriptView.ordinary_length, h, hlen])
              exact hfixed 31 (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
                (.payload ctx.message) (by decide) hround)
        · by_cases hrho : n = 32
          · subst n
            rw [UnifiedDecoder.component_rho] at hcomponent
            obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
              DecoderStateList.lift_sound (JointUnifiedDecoder.decode p pub 27 4) pub a T
                own pend g hcomponent
            have hfixed_rho : ∀ ctx,
                JointContext.parse p pub.pubBytes pub.tag 27 4 a T = some ctx →
                ctx.records.length = 31 →
                ∀ as, as.length =
                    (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).length →
                  independentMean
                    (UnifiedSampler.samp p hD 32
                      (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
                        (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as))
                      (.payload ctx.nextMessage)).toProgram
                    (fun w => obs
                      (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
                        (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as),
                        .payload ctx.nextMessage, w.2)) ≤ B := by
              intro ctx hp hlen as has
              have hround := JointTranscriptView.parsed_prefix_length p pub 27 4 a T
                ctx hp hlen as
              exact hfixed 32
                (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
                  (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as))
                (.payload ctx.nextMessage) (by decide) hround
            have hbound := JointUnifiedBound.decoded_bound p hD pub 27 4 a T
              own₀ pend₀ g₀ hdecode obs B hfixed_rho
            cases heq
            rw [DecoderStateList.lifted_law]
            exact hbound
          · have hopening_lo : 27 ≤ n := by omega
            have hopening_hi : n < 31 := by omega
            rw [UnifiedDecoder.component_opening p hD pub n hopening_lo hopening_hi]
              at hcomponent
            obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
              DecoderStateList.lift_sound (UnifiedOpeningDecoder.decode p pub) pub a T
                own pend g hcomponent
            have hfixed_opening : ∀ ctx,
                UnifiedOpeningDecoder.parse p pub a T = some ctx →
                27 ≤ ctx.records.length → ctx.records.length < 31 →
                ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
                  independentMean
                    (UnifiedSampler.samp p hD ctx.records.length
                      (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
                    (fun w => obs
                      (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)) ≤ B := by
              intro ctx hp hlo hhi as has
              have hround :
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = ctx.records.length := by
                simp [UnifiedSemanticLaw.mkPrefix, TranscriptView.ordinary_length,
                  PrefixRecordLength.fromAnswers_length]
              exact hfixed ctx.records.length
                (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)
                (by omega) hround
            have hbound := UnifiedOpeningLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
              hdecode obs B hfixed_opening
            cases heq
            rw [DecoderStateList.lifted_law]
            exact hbound

theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedDecoder.decode p hD pub a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ (i : Nat) (P : UnifiedSampler.Prefix M Cv L) (m : Message M),
      i < 33 → P.rounds.length = i →
        independentMean (UnifiedSampler.samp p hD i P m).toProgram
          (fun w => obs (P, m, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨n, hn, hcomponent⟩ := UnifiedDecoder.decode_sound p hD pub a T own pend g hd
  exact component_bound p hD pub n hn a T own pend g hcomponent obs B hfixed

#print axioms component_bound
#print axioms decoded_bound

end AspisR1.UnifiedDecoderBound
end
