import R1UnifiedReseedDecoder
import R1UnifiedSemanticLaw

/-! The reseeded completing decoder has the unified row-26 sampler law.
Bound transfer keeps the fixed-prefix premise explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedReseedLaw

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem background_sampler_law (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (T : Table (Addr L) State)
    (ctx : UnifiedSemanticContext.Context M) (a : Addr L)
    (obs : JointTranscriptView.Output M Cv L → ℚ)
    (hlen : ctx.records.length = 26) :
    blaw (UnifiedSemanticDecoder.output p pub T ctx) obs
      (UnifiedReseedDecoder.own p pub a)
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) =
    pmean (fun as => independentMean
      (UnifiedSampler.samp p hD 26 (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
        (.payload ctx.message)).toProgram
      (fun w => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as,
        .payload ctx.message, w.2)))
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) := by
  unfold UnifiedSemanticDecoder.output
  rw [BackgroundLawMap.blaw_map]
  have hbackground := ReseedSamplerLaw.background_law p a
    (OpeningReseedFrame.addr pub.tag (by have := pub.initFits; omega))
    ctx.records.length ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none))
    (PrefixAnswers.fromAnswers p T 0 ctx.records)
    (fun out => obs (UnifiedSemanticDecoder.view pub ctx out))
  have hb : blaw (PrefixNextLaw.output p T ctx.records)
      (fun out => obs (UnifiedSemanticDecoder.view pub ctx out))
      (UnifiedReseedDecoder.own p pub a)
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) =
      pmean (fun as => mean (fun b => mean (fun y =>
        obs (UnifiedSemanticDecoder.view pub ctx
          (PrefixAnswers.fromAnswers p T 0 ctx.records as, (p.σ ctx.records.length b, y))))))
        ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) := by
    change blaw (fun y as =>
      (PrefixAnswers.fromAnswers p T 0 ctx.records
        (as.take (PrefixAnswers.missing p T ctx.records).length),
        (p.σ ctx.records.length
          ((as.drop (PrefixAnswers.missing p T ctx.records).length).headD default), y)))
      (fun out => obs (UnifiedSemanticDecoder.view pub ctx out))
      (UnifiedReseedDecoder.own p pub a)
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) = _
    simpa only [List.length_map, UnifiedReseedDecoder.own] using hbackground
  rw [hb]
  apply BackgroundMean.pmean_congr_length
  intro as _
  have hlaw := UnifiedSampler.unified_law p hD 26
    (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)
    (fun ch => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, ch))
    (by decide) (by simp [UnifiedSampler.messageValid])
  rw [hlaw, hlen]
  rfl

theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedReseedDecoder.decode p pub a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ ctx, UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx →
      ctx.records.length = 26 →
      ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
        independentMean
          (UnifiedSampler.samp p hD 26 (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
            (.payload ctx.message)).toProgram
          (fun w => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as,
            .payload ctx.message, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨ctx, hp, hlen, ht⟩ := UnifiedReseedDecoder.decode_sound p pub a T own pend g hd
  cases ht
  rw [background_sampler_law p hD pub T ctx a obs hlen]
  apply pmean_le
  intro as has
  exact hfixed ctx hp hlen as (by simpa only [List.length_map] using has)

#print axioms background_sampler_law
#print axioms decoded_bound

end AspisR1.UnifiedReseedLaw
end
