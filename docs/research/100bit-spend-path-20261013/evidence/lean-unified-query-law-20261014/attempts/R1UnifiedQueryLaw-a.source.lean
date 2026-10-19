import R1UnifiedQueryDecoder
import R1QueryBackgroundLaw
import R1UnifiedSamplerLaw

/-! Exact background and independent-sampler laws for the fixed query row.
Any bound below is conditional on an explicit fixed-prefix bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedQueryLaw

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem background_sampler_law (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (T : Table (Addr L) State)
    (ctx : UnifiedSemanticContext.Context M) (a : Addr L)
    (obs : JointTranscriptView.Output M Cv L → ℚ)
    (hlen : ctx.records.length = 31) :
    blaw (UnifiedQueryDecoder.output p pub T ctx) obs (UnifiedQueryDecoder.own p a)
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) =
    pmean (fun as => independentMean
      (UnifiedSampler.samp p hD 31
        (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
      (fun w => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as,
        .payload ctx.message, w.2)))
      ((PrefixAnswers.missing p T ctx.records).map fun b => (b, none)) := by
  let pend := (PrefixAnswers.missing p T ctx.records).map fun b => (b, (none : Option State))
  have hlenAs (as : List State) (has : as.length = pend.length) :
      as.length = (PrefixAnswers.missing p T ctx.records).length := by
    simpa [pend] using has
  unfold UnifiedQueryDecoder.own
  simp only [blaw]
  rw [QueryBackgroundLaw.blaw_chainBS p (UnifiedQueryDecoder.output p pub T ctx)
    obs 8]
  rw [← R0C.V3.pmean_mean_comm pend (fun s as => Q22.chainE
    (fun bs ys => obs (UnifiedQueryDecoder.output p pub T ctx ([s] ++ ys) (as ++ bs))) 8)]
  apply BackgroundMean.pmean_congr_length
  intro as has
  have haslen := hlenAs as has
  rw [UnifiedSampler.row_query p hD
    (UnifiedSemanticLaw.mkPrefix p pub T ctx as) ctx.message]
  simp only [QuerySamplerBridge.sampler, Sampler.toProgram, independentMean]
  apply mean_congr
  intro s
  have hout (moreBs moreXs : List State) :
      UnifiedQueryDecoder.output p pub T ctx ([s] ++ moreXs) (as ++ moreBs) =
        (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message,
          UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 moreBs moreXs s)) := by
    rw [UnifiedQueryDecoder.output_append p pub T ctx ([s] ++ moreXs) as moreBs haslen]
    rfl
  have hchain := QueryBackgroundLaw.independent_chain_law p
    (fun moreBs moreXs => UnifiedSampler.liftQuery
      (Q22.scanOut 8 Q22.q0 moreBs moreXs s))
    (fun ch => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as,
      .payload ctx.message, ch)) 8 s [] []
  have houtput : Q22.chainE
      (fun moreBs moreXs =>
        obs (UnifiedQueryDecoder.output p pub T ctx ([s] ++ moreXs) (as ++ moreBs))) 8 =
      Q22.chainE
        (fun moreBs moreXs => obs
          (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message,
            UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 moreBs moreXs s))) 8 := by
    apply congrArg (Q22.chainE · 8)
    funext moreBs moreXs
    exact congrArg obs (hout moreBs moreXs)
  rw [houtput, ← hchain]

theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedQueryDecoder.decode p pub a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ ctx, UnifiedOpeningDecoder.parse p pub a T = some ctx →
      ctx.records.length = 31 →
      ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
        independentMean
          (UnifiedSampler.samp p hD 31
            (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
          (fun w => obs (UnifiedSemanticLaw.mkPrefix p pub T ctx as,
            .payload ctx.message, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨ctx, hp, hlen, heq⟩ := UnifiedQueryDecoder.decode_sound p pub a T own pend g hd
  cases heq
  rw [background_sampler_law p hD pub T ctx a obs hlen]
  apply pmean_le
  intro as has
  exact hfixed ctx hp hlen as (by simpa only [List.length_map] using has)

#print axioms background_sampler_law
#print axioms decoded_bound

end AspisR1.UnifiedQueryLaw
end
