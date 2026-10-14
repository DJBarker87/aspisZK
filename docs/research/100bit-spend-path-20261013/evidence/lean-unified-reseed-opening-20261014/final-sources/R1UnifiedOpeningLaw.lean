import R1UnifiedOpeningDecoder
import R1UnifiedSemanticLaw

/-! Transfer the ordinary-prefix completion law to the unified opening
sampler. The bound is conditional on a fixed-prefix bound; no numerical
security claim or independence of an arbitrary oracle trace is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOpeningLaw

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
    (hlo : 27 ≤ ctx.records.length) (hhi : ctx.records.length < 31) :
    blaw (UnifiedSemanticDecoder.output p pub T ctx) obs (QueryNextLaw.own p a)
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) =
    pmean (fun as => independentMean
      (UnifiedSampler.samp p hD ctx.records.length (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
        (.payload ctx.message)).toProgram
      (fun w => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)))
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) := by
  unfold UnifiedSemanticDecoder.output
  rw [BackgroundLawMap.blaw_map, PrefixNextLaw.background_law]
  apply BackgroundMean.pmean_congr_length
  intro as _
  have hlaw := UnifiedSampler.unified_law p hD ctx.records.length
    (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)
    (fun ch => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, ch))
    (by omega) (by
      cases hn : ctx.records.length with
      | zero => omega
      | succ j => simp [UnifiedSampler.messageValid])
  rw [hlaw]
  rfl

theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedOpeningDecoder.decode p pub a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ ctx, UnifiedOpeningDecoder.parse p pub a T = some ctx →
      27 ≤ ctx.records.length → ctx.records.length < 31 →
      ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
        independentMean
          (UnifiedSampler.samp p hD ctx.records.length (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
            (.payload ctx.message)).toProgram
          (fun w => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨ctx, hp, hlo, hhi, ht⟩ :=
    UnifiedOpeningDecoder.decode_sound p pub a T own pend g hd
  cases ht
  rw [background_sampler_law p hD pub T ctx a obs hlo hhi]
  apply pmean_le
  intro as has
  exact hfixed ctx hp hlo hhi as (by simpa only [List.length_map] using has)

#print axioms background_sampler_law
#print axioms decoded_bound

end AspisR1.UnifiedOpeningLaw
end
