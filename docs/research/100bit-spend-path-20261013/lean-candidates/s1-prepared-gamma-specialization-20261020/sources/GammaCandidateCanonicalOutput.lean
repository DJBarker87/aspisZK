import GammaCandidateDecodedFieldRank
import CurrentSamplerCanonicalV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GammaCaller.DigitsModel

def samplerWideToGamma (v : AspisR1Post25Sampler.field.WideExact) : GammaWide :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
    ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩

theorem candidate_gamma_success_coordinate_bounds (block : CandidateBytes32)
    (out : GammaWide)
    (h : AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block=.ok out) :
    out.c0.c0.a.val<2147483647 ∧ out.c0.c0.b.val<2147483647 ∧
    out.c0.c1.a.val<2147483647 ∧ out.c0.c1.b.val<2147483647 ∧
    out.c1.c0.a.val<2147483647 ∧ out.c1.c0.b.val<2147483647 ∧
    out.c1.c1.a.val<2147483647 ∧ out.c1.c1.b.val<2147483647 := by
  obtain ⟨digits,hdecode,hcanonical,hvalue,hfield⟩ := candidate_gamma_decode_fieldRank block out h
  change (do let value ← AspisR1Post25Sampler.sampler.decode8 digits
             .ok (samplerWideToGamma value))=.ok out at hdecode
  cases hd : AspisR1Post25Sampler.sampler.decode8 digits with
  | fail e => simp only [hd,bind_tc_fail] at hdecode; cases hdecode
  | div => simp only [hd,bind_tc_div] at hdecode; cases hdecode
  | ok value =>
    simp only [hd,bind_tc_ok] at hdecode
    have he : samplerWideToGamma value=out := Result.ok.inj hdecode
    rw [←he]
    exact AspisR1Post25SamplerCanonical.decode8_success_bounds digits value hd

#print axioms candidate_gamma_success_coordinate_bounds
end AspisR1GammaCaller.DigitsModel
