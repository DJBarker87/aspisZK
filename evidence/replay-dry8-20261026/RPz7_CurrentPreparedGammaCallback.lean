import RPz7_CurrentPreparedOriginalPayload
import GammaCandidateCanonicalOutput
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete

def gammaToPublic (v : AspisR1GammaCaller.DigitsModel.GammaWide) : PE :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
    ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩

def candidateGammaPublic (block : Array U8 32#usize) : Result PE := do
  let out ← AspisR1GammaCaller.sampler.gamma_sample
    AspisR1GammaCaller.DigitsModel.candidateGammaHelpers block
  ok (gammaToPublic out)

theorem candidateGammaPublic_success_canonical (block : Array U8 32#usize) (out : PE)
    (h : candidateGammaPublic block=ok out) : Canonical (toClaimE out) := by
  unfold candidateGammaPublic at h
  cases hg : AspisR1GammaCaller.sampler.gamma_sample
      AspisR1GammaCaller.DigitsModel.candidateGammaHelpers block with
  | fail e => simp only [hg,bind_tc_fail] at h; cases h
  | div => simp only [hg,bind_tc_div] at h; cases h
  | ok value =>
    simp only [hg,bind_tc_ok] at h
    have he : gammaToPublic value=out := Result.ok.inj h
    rw [←he]
    obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
      AspisR1GammaCaller.DigitsModel.candidate_gamma_success_coordinate_bounds block value hg
    exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

#print axioms candidateGammaPublic_success_canonical
end AspisR1ClaimPreparedBridge
