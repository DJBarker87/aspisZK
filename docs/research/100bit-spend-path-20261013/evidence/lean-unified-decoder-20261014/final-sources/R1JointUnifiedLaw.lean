import R1JointTranscriptView

/-! The joint decoder's terminal challenge has the unified sampler law after
the fixed completed-prefix answers are averaged over the same background. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointUnifiedLaw

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem background_sampler_law (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L) (c : Addr L)
    (obs : JointTranscriptView.Output M Cv L → ℚ)
    (hlen : ctx.records.length = 31) :
    blaw (fun x as => JointTranscriptView.view pub (JointDecoder.output p T ctx x as))
      obs (QueryNextLaw.own p c)
      ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map
        fun b => (b, none)) =
    pmean (fun as => independentMean
      (UnifiedSampler.samp p hD 32
        (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
          (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as))
        (.payload ctx.nextMessage)).toProgram
      (fun w => obs
        (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
          (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as),
          .payload ctx.nextMessage, w.2)))
      ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map
        fun b => (b, none)) := by
  rw [BackgroundLawMap.blaw_map]
  rw [JointDecoder.output_law]
  apply BackgroundMean.pmean_congr_length
  intro as _
  let P := JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
    (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as)
  let challengeObs : TranscriptView.Challenge Cv → ℚ :=
    fun ch => obs (P, .payload ctx.nextMessage, ch)
  have hlaw := UnifiedSampler.unified_law p hD 32 P (.payload ctx.nextMessage)
    challengeObs (by decide) (by simp [UnifiedSampler.messageValid])
  rw [hlaw]
  apply mean_congr
  intro b
  apply mean_congr
  intro x
  simp only [JointTranscriptView.view, JointDecoder.attach, P, challengeObs]
  rw [hlen]

#print axioms background_sampler_law

end AspisR1.JointUnifiedLaw
end
