import R1JointUnifiedDecoder
import R1JointUnifiedLaw

/-! Transfer a fixed-prefix terminal-challenge bound through the parsed
unified joint decoder. This is a generic bound-transfer lemma only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointUnifiedBound

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (semanticFuel openingFuel : Nat)
    (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : JointUnifiedDecoder.decode p pub semanticFuel openingFuel c T =
      some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ ctx,
      JointContext.parse p pub.pubBytes pub.tag semanticFuel openingFuel c T = some ctx →
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
              .payload ctx.nextMessage, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨ctx, hparse, hlen, hshape⟩ :=
    JointUnifiedDecoder.decode_sound p pub semanticFuel openingFuel c T own pend g hd
  cases hshape
  rw [JointUnifiedLaw.background_sampler_law p hD pub T ctx c obs hlen]
  apply pmean_le
  intro as has
  have hlenAs : as.length =
      (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).length := by
    simpa only [List.length_map] using has
  exact hfixed ctx hparse hlen as hlenAs

#print axioms decoded_bound

end AspisR1.JointUnifiedBound
end
