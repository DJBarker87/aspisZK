import CurrentSamplerCanonicalV5
import CurrentPreparedClaimCarriers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25SamplerPreparedCarrier
open AspisR1Post25SamplerCanonical AspisR1ClaimPreparedBridge
abbrev CandidateE := AspisR1Post25Sampler.field.WideExact
abbrev PE := AspisR1ClaimPreparedBridge.PE
abbrev CE := AspisR1ClaimPreparedBridge.CE

def candidateToPE (x : CandidateE) : PE :=
  { c0 :=
      { c0 := { a := x.c0.c0.a, b := x.c0.c0.b },
        c1 := { a := x.c0.c1.a, b := x.c0.c1.b } },
    c1 :=
      { c0 := { a := x.c1.c0.a, b := x.c1.c0.b },
        c1 := { a := x.c1.c1.a, b := x.c1.c1.b } } }

def candidateToCE (x : CandidateE) : CE := toClaimE (candidateToPE x)

theorem ordinary_sample_success_CE_coordinate_bounds
    (block : Array U8 32#usize) (out : CandidateE)
    (h : AspisR1Post25Sampler.sampler.ordinary_sample block = .ok out) :
    (candidateToCE out).c0.c0.a.val < 2147483647 ∧
    (candidateToCE out).c0.c0.b.val < 2147483647 ∧
    (candidateToCE out).c0.c1.a.val < 2147483647 ∧
    (candidateToCE out).c0.c1.b.val < 2147483647 ∧
    (candidateToCE out).c1.c0.a.val < 2147483647 ∧
    (candidateToCE out).c1.c0.b.val < 2147483647 ∧
    (candidateToCE out).c1.c1.a.val < 2147483647 ∧
    (candidateToCE out).c1.c1.b.val < 2147483647 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
    AspisR1Post25SamplerCanonical.ordinary_sample_success_bounds block out h
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩

#print axioms ordinary_sample_success_CE_coordinate_bounds
end AspisR1Post25SamplerPreparedCarrier
