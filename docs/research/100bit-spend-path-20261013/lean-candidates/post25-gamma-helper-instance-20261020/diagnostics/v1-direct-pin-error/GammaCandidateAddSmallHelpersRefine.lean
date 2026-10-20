import GammaCandidateLowQuotient
import GammaCallerRankModel
import IndexedCandidateAddSmallWrapperNatModelV3
import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace AspisR1GammaCaller.DigitsModel

open AspisR1
open AspisR1.SamplerNatModel
open AspisR1.SamplerAddDigits
open AspisR1.ExtractedIndexedAddSmallWrapperNatModelV1

abbrev CandidateDigits := Array U32 8#usize
abbrev CandidateBytes32 := Array U8 32#usize

private theorem canonical_for_indexed (ds : CandidateDigits) (h : Canonical ds) :
    AspisR1.ExtractedIndexedAddSmallNatModelV1.Canonical ds := by
  intro j hj
  have hlen : j < (values ds).length := by
    simp only [values, List.length_map]
    have hds := ds.property
    change ds.val.length = (8#usize).val at hds
    have h8 : (8#usize).val = 8 := by decide
    omega
  have hmem : (values ds)[j]'hlen ∈ values ds := List.getElem_mem hlen
  have hvalue : (values ds)[j]'hlen =
      AspisR1.ExtractedIndexedAddSmallNatModelV1.cell ds j hj := by
    simp [values, AspisR1.ExtractedIndexedAddSmallNatModelV1.cell, hj, hlen]
  rw [← hvalue]
  exact h ((values ds)[j]'hlen) hmem

def candidateHelpers (decode : CandidateDigits → Result field.WideExact) : GammaHelpers where
  low := fun block => AspisR1Post25Sampler.sampler.low_base_p_digits block
  add := fun ds n => AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p ds n
  decode := decode

theorem candidate_helpers_refine (decode : CandidateDigits → Result field.WideExact) :
    HelpersRefine (candidateHelpers decode) := by
  constructor
  · intro block ds q h
    apply low_candidate_refines
    exact h
  · intro ds n wrapped out hcanon hn h
    have hcanon' := canonical_for_indexed ds hcanon
    obtain ⟨outCarry, outDigits, hexec, hvalues, hcarry⟩ :=
      AspisR1.ExtractedIndexedAddSmallWrapperNatModelV1.add_small_base_p_refines_addDigits
        ds n hcanon' hn
    have h' :
        AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p ds n =
          .ok (outCarry != 0#u32, outDigits) := hexec
    have heq : (outCarry != 0#u32, outDigits) = (wrapped, out) :=
      Result.ok.inj (h'.symm.trans h)
    rcases heq with ⟨rfl, rfl⟩
    refine ⟨hvalues, ?_⟩
    constructor
    · intro hfalse
      have hzero : outCarry = 0#u32 := by
        by_contra hne
        have htrue : (outCarry != 0#u32) = true := by simpa using hne
        simp [htrue] at hfalse
      have hv := congrArg UScalar.val hzero
      simpa [hcarry] using hv
    · intro hzero
      have hv : outCarry.val = 0 := hcarry.trans hzero
      have hval : outCarry = 0#u32 := UScalar.eq_of_val_eq hv
      simp [hval]

theorem candidate_gamma_rank_success
    (decode : CandidateDigits → Result field.WideExact)
    (block : CandidateBytes32) (out : field.WideExact)
    (h : AspisR1GammaCaller.sampler.gamma_sample (candidateHelpers decode) block = .ok out) :
    ∃ ds : CandidateDigits,
      decode ds = .ok out ∧ Canonical ds ∧
      digitsValue P (values ds) = rank block % (P^8 - 1) + 1 ∧
      0 < digitsValue P (values ds) ∧ digitsValue P (values ds) < P^8 := by
  exact gamma_rank_success (candidateHelpers decode) (candidate_helpers_refine decode) block out h

#print axioms candidate_helpers_refine
#print axioms candidate_gamma_rank_success

end AspisR1GammaCaller.DigitsModel
