import R1UnifiedInitialDecoder

/-! The initial completing decoder has the unified row-zero sampler law.
The optional bound below retains its fixed-prefix bound as an explicit
premise; no numerical soundness bound is supplied by this module. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedInitialLaw

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem sampler_law (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (c1 : State)
    (obs : JointTranscriptView.Output M Cv L → ℚ) :
    blaw (UnifiedInitialDecoder.output p pub c1) obs
      (InitialSamplerLaw.own p a (PublicInitFrame.row0 p hD)) [] =
    independentMean (UnifiedSampler.samp p hD 0 (emptyPrefix pub) (.initial c1)).toProgram
      (fun w => obs (emptyPrefix pub, .initial c1, w.2)) := by
  change blaw (fun x bs => UnifiedInitialDecoder.view pub
    (c1, (p.σ 0 (bs.headD default), x))) obs
      (InitialSamplerLaw.own p a (PublicInitFrame.row0 p hD)) [] = _
  rw [InitialSamplerLaw.own_law p a (PublicInitFrame.row0 p hD) 0
    (fun ch => UnifiedInitialDecoder.view pub (c1, ch)) obs]
  rw [UnifiedSampler.row_zero]
  exact (DuplexSamplers.initial_law p
    (PublicInitFrame.addr pub.pubBytes pub.initFits c1) (PublicInitFrame.row0 p hD)
    0 liftChallenge (fun ch => obs (emptyPrefix pub, .initial c1, ch))).symm

theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedInitialDecoder.decode p hD pub a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ c1, PublicInitParse.parse pub.pubBytes a = some c1 →
      independentMean (UnifiedSampler.samp p hD 0 (emptyPrefix pub) (.initial c1)).toProgram
        (fun w => obs (emptyPrefix pub, .initial c1, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨c1, hp, ht⟩ := UnifiedInitialDecoder.decode_sound p hD pub a T own pend g hd
  cases ht
  rw [sampler_law]
  exact hfixed c1 hp

#print axioms sampler_law
#print axioms decoded_bound

end AspisR1.UnifiedInitialLaw
end
