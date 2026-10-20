import GammaCandidateDecodedFieldRank
import IndexedCandidateOuterByteOutputSuccessV5

set_option autoImplicit false

open Aeneas Aeneas.Std Result WP

namespace AspisR1GammaCaller.DigitsModel

open AspisR1
open AspisR1.SamplerMachineBounds
open AspisR1.SamplerNatModel
open AspisR1.SamplerAddDigits
open AspisR1.SamplerAddBridge
open AspisR1.SourceSamplerByteRank
open AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5
open AspisR1.ExtractedIndexedAddSmallWrapperNatModelV1
open AspisR1.ExtractedIndexedAddSmallNatModelV1
open AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3
open AspisR1Post25Sampler

private abbrev Pn : Nat := AspisR1.SamplerMachineBounds.P
private def gammaOfDecoded (v : AspisR1Post25Sampler.field.WideExact) : GammaWide :=
  ⟨⟨⟨v.c0.c0.a, v.c0.c0.b⟩, ⟨v.c0.c1.a, v.c0.c1.b⟩⟩,
    ⟨⟨v.c1.c0.a, v.c1.c0.b⟩, ⟨v.c1.c1.a, v.c1.c1.b⟩⟩⟩

private def digitAt (digits : Digits) (i : Fin 8) : U32 :=
  digits.val[i.val]'(by
    have hd := digits.property
    change digits.val.length = (8#usize).val at hd
    have h8 : (8#usize).val = 8 := by decide
    omega)

private theorem canonical_fin (digits : Digits) (hcanonical : Canonical digits) :
    ∀ i : Fin 8, (digitAt digits i).val < Pn := by
  intro i
  have hmem : (digitAt digits i).val ∈ values digits := by
    unfold digitAt values
    rw [List.mem_map]
    exact ⟨digits.val[i.val]'(by
      have hd := digits.property
      change digits.val.length = (8#usize).val at hd
      have h8 : (8#usize).val = 8 := by decide
      omega), List.getElem_mem _, rfl⟩
  exact hcanonical _ hmem

private theorem candidate_decode_total (digits : Digits)
    (hcanonical : Canonical digits) :
    ∃ out : GammaWide, candidateGammaHelpers.decode digits = .ok out := by
  have hcanonicalFin := canonical_fin digits hcanonical
  obtain ⟨decoded, hdecoded, _⟩ := decode8_candidate_eq_retained digits hcanonicalFin
  refine ⟨gammaOfDecoded decoded, ?_⟩
  change (do
      let value ← AspisR1Post25Sampler.sampler.decode8 digits
      .ok (gammaOfDecoded value)) = .ok (gammaOfDecoded decoded)
  rw [hdecoded]
  rfl

private theorem increment_success (q : U32) (hq : q.val ≤ 256) :
    ∃ n : U32, (q + 1#u32 : Result U32) = .ok n ∧ n.val = q.val + 1 := by
  have hs : (q + 1#u32 : Result U32) ⦃z => z.val = q.val + 1⦄ := by
    apply UScalar.add_spec
    change q.val + 1 ≤ UScalar.max UScalarTy.U32
    have hc : 257 ≤ UScalar.max UScalarTy.U32 := by
      rw [UScalar.max_UScalarTy_U32_eq]
      norm_num [U32.max, U32.numBits]
    omega
  obtain ⟨n, hn, hval⟩ := WP.spec_imp_exists hs
  exact ⟨n, hn, hval⟩

private theorem pair_bind_success_intro {α β γ : Type} (m : Result (α × β))
    (a : α) (b : β) (hm : m = .ok (a,b)) (k : α → β → Result γ)
    (out : γ) (hk : k a b = .ok out) :
    (do let (x,y) ← m; k x y) = .ok out := by
  rw [hm]
  exact hk

private theorem pair_let {α β γ : Type} (a : α) (b : β)
    (k : α → β → γ) :
    (let (x,y) := (a,b); k x y) = k a b := by
  rfl

private theorem bind_pair_ok {α β γ : Type} (a : α) (b : β)
    (k : α → β → Result γ) :
    (do let (x,y) ← (Result.ok (a,b) : Result (α × β)); k x y) = k a b := by
  rfl

private theorem values_length_eight (digits : Digits) : (values digits).length = 8 := by
  simp only [values, List.length_map]
  have hd := digits.property
  change digits.val.length = (8#usize).val at hd
  have h8 : (8#usize).val = 8 := by decide
  omega

private theorem canonical_for_indexed (digits : Digits) (hcanonical : Canonical digits) :
    AspisR1.ExtractedIndexedAddSmallNatModelV1.Canonical digits := by
  intro j hj
  have hlen : j < digits.val.length := by
    have hd := digits.property
    change digits.val.length = (8#usize).val at hd
    have h8 : (8#usize).val = 8 := by decide
    omega
  have hmem : (digits.val[j]'hlen).val ∈ values digits := by
    rw [values]
    exact List.mem_map.mpr ⟨digits.val[j]'hlen, List.getElem_mem hlen, rfl⟩
  have h := hcanonical _ hmem
  change (digits.val[j]'(by
    have hd := digits.property
    change digits.val.length = (8#usize).val at hd
    have h8 : (8#usize).val = 8 := by decide
    omega)).val < Pn at h
  exact h

private theorem second_carry_zero
    (block : Bytes32) (digits : Digits) (q n carry1 : U32)
    (hvalues : values digits = ordinaryDigits (rank block))
    (hq : q.val = rank block / Pn^8)
    (hn : n.val = q.val + 1)
    (hcarry1 : carry1.val = (addDigits Pn n.val (values digits)).2)
    (hcarry1pos : 0 < carry1.val) :
    (addDigits Pn 1 (addDigits Pn n.val (values digits)).1).2 = 0 := by
  have hlen : (values digits).length = 8 := values_length_eight digits
  have hfirst := addDigits_mod_div (p := Pn) P_pos n.val (values digits)
  rw [hlen] at hfirst
  have hr : digitsValue Pn (values digits) = rank block % Pn^8 := by
    rw [hvalues, ordinaryDigits_value]
  have hNpos : 0 < Pn^8 := by
    have hN : 2 ≤ Pn^8 := by simpa [Pn] using two_le_P8
    omega
  have hrlt : rank block % Pn^8 < Pn^8 := Nat.mod_lt _ hNpos
  have hqsmall : q.val < Pn^8 - 1 := by
    rw [hq]
    exact rank_div_P8_lt_P8_sub_one (rank_lt block)
  have hsumlt : rank block % Pn^8 + q.val + 1 < 2 * Pn^8 := by
    omega
  have hfirstcarry : (addDigits Pn n.val (values digits)).2 > 0 := by
    rw [← hcarry1]
    exact hcarry1pos
  have hdivpos :
      0 < (rank block % Pn^8 + (q.val + 1)) / Pn^8 := by
    have hf := hfirstcarry
    rw [hfirst.2, hr, hn] at hf
    simpa [Nat.add_assoc] using hf
  have hge : Pn^8 ≤ rank block % Pn^8 + q.val + 1 := by
    have hone : 1 ≤ (rank block % Pn^8 + (q.val + 1)) / Pn^8 := by omega
    have hprod : Pn^8 ≤ Pn^8 *
        ((rank block % Pn^8 + (q.val + 1)) / Pn^8) :=
      by simpa using Nat.mul_le_mul_left (Pn^8) hone
    have hdecomp :
        (rank block % Pn^8 + (q.val + 1)) % Pn^8 +
          Pn^8 * ((rank block % Pn^8 + (q.val + 1)) / Pn^8) =
        rank block % Pn^8 + (q.val + 1) := by
      exact Nat.mod_add_div _ _
    have hle : Pn^8 *
        ((rank block % Pn^8 + (q.val + 1)) / Pn^8) ≤
        (rank block % Pn^8 + (q.val + 1)) % Pn^8 +
          Pn^8 * ((rank block % Pn^8 + (q.val + 1)) / Pn^8) := by
      exact Nat.le_add_left
        (Pn^8 * ((rank block % Pn^8 + (q.val + 1)) / Pn^8))
        ((rank block % Pn^8 + (q.val + 1)) % Pn^8)
    have hge' : Pn^8 ≤ rank block % Pn^8 + (q.val + 1) :=
      le_trans hprod (le_trans hle (by rw [hdecomp]))
    omega
  have hrem : (rank block % Pn^8 + q.val + 1) % Pn^8 =
      rank block % Pn^8 + q.val + 1 - Pn^8 := by
    rw [Nat.mod_eq_sub_mod hge]
    exact Nat.mod_eq_of_lt (by omega)
  have hlast : rank block % Pn^8 + q.val + 1 - Pn^8 + 1 < Pn^8 :=
    AspisR1.SamplerCarry.wrapped_result_lt (by simpa [Pn] using two_le_P8)
      hqsmall hrlt hge
  have hsecond := addDigits_mod_div (p := Pn) P_pos 1
    (addDigits Pn n.val (values digits)).1
  rw [addDigits_length, hlen] at hsecond
  have hrem' :
      (rank block % Pn^8 + (q.val + 1)) % Pn^8 =
        rank block % Pn^8 + q.val + 1 - Pn^8 := by
    simpa [Nat.add_assoc] using hrem
  have hsecondCarry := hsecond.2
  rw [hfirst.1, hr, hn, hrem'] at hsecondCarry
  rw [Nat.div_eq_of_lt hlast] at hsecondCarry
  simpa [hn] using hsecondCarry

theorem candidate_gamma_total (block : Bytes32) :
    ∃ out : GammaWide,
      AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block = .ok out := by
  obtain ⟨_, lowDigits, q, hlow, _, _, _⟩ := low_base_p_digits_success block
  have hlowModel := low_candidate_refines block lowDigits q hlow
  have hq : q.val = rank block / Pn^8 := hlowModel.2
  have hq256 : q.val ≤ 256 := by
    rw [hq]
    exact rank_div_P8_le_256 (rank_lt block)
  obtain ⟨n, hn, hnval⟩ := increment_success q hq256
  have hcanonical : Canonical lowDigits := by
    unfold Canonical
    rw [hlowModel.1]
    exact lowDigits_canonical P_pos 8 (rank block)
  have hnBound : n.val ≤ 257 := by omega
  have hcanonicalIndexed := canonical_for_indexed lowDigits hcanonical
  obtain ⟨carry1, digits1, hadd1, hvalues1, hcarry1⟩ :=
    add_small_base_p_refines_addDigits lowDigits n hcanonicalIndexed hnBound
  have hvalues1' : values digits1 =
      (addDigits Pn n.val (values lowDigits)).1 := by
    change ExtractedIndexedAddSmallNatModelV1.values digits1 =
      (addDigits Pn n.val (ExtractedIndexedAddSmallNatModelV1.values lowDigits)).1
    exact hvalues1
  have hcarry1' : carry1.val =
      (addDigits Pn n.val (values lowDigits)).2 := by
    change carry1.val =
      (addDigits Pn n.val (ExtractedIndexedAddSmallNatModelV1.values lowDigits)).2
    exact hcarry1
  have hcanonical1 : Canonical digits1 := by
    unfold Canonical
    rw [hvalues1']
    exact addDigits_output_digits_lt Pn n.val (values lowDigits) P_pos
  by_cases hzero : carry1 = 0#u32
  · have hbool : (carry1 != 0#u32) = false := by simp [hzero]
    obtain ⟨out, hdecode⟩ := candidate_decode_total digits1 hcanonical1
    have hlow' : candidateGammaHelpers.low block = .ok (lowDigits, q) := by
      change AspisR1Post25Sampler.sampler.low_base_p_digits block = .ok (lowDigits, q)
      exact hlow
    have hadd1' : candidateGammaHelpers.add lowDigits n =
        .ok (carry1 != 0#u32, digits1) := by
      change AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p
        lowDigits n = .ok (carry1 != 0#u32, digits1)
      exact hadd1
    refine ⟨out, ?_⟩
    unfold AspisR1GammaCaller.sampler.gamma_sample
    rw [hlow']
    rw [bind_pair_ok]
    rw [hn]
    simp only [bind_tc_ok]
    rw [hadd1']
    rw [bind_pair_ok]
    rw [hbool]
    simp only [Bool.false_eq_true, if_false, bind_tc_ok, hdecode]
  · have hcarry1pos : 0 < carry1.val := by
      have hne : carry1.val ≠ 0 := by
        intro hz
        exact hzero (UScalar.eq_of_val_eq hz)
      omega
    have hbool : (carry1 != 0#u32) = true := by simp [hzero]
    have hcanonical1Indexed := canonical_for_indexed digits1 hcanonical1
    obtain ⟨carry2, digits2, hadd2, hvalues2, hcarry2⟩ :=
      add_small_base_p_refines_addDigits digits1 1#u32 hcanonical1Indexed (by decide)
    have hcarry2zero := second_carry_zero block lowDigits q n carry1
      hlowModel.1 hlowModel.2 hnval hcarry1' hcarry1pos
    have hcarry2' : carry2.val =
        (addDigits Pn 1 (values digits1)).2 := by
      change carry2.val =
        (addDigits Pn (1#u32).val (ExtractedIndexedAddSmallNatModelV1.values digits1)).2
      rw [show (1#u32).val = 1 by rfl]
      exact hcarry2
    have hcarry2val : carry2.val = 0 := by
      rw [hcarry2', hvalues1', hcarry2zero]
    have hcarry2zeroU : carry2 = 0#u32 := UScalar.eq_of_val_eq hcarry2val
    have hcanonical2 : Canonical digits2 := by
      unfold Canonical
      have hvalues2' : values digits2 =
          (addDigits Pn 1 (values digits1)).1 := by
        change ExtractedIndexedAddSmallNatModelV1.values digits2 =
          (addDigits Pn (1#u32).val
            (ExtractedIndexedAddSmallNatModelV1.values digits1)).1
        rw [show (1#u32).val = 1 by rfl]
        exact hvalues2
      rw [hvalues2']
      exact addDigits_output_digits_lt Pn 1 (values digits1) P_pos
    obtain ⟨out, hdecode⟩ := candidate_decode_total digits2 hcanonical2
    have hlow' : candidateGammaHelpers.low block = .ok (lowDigits, q) := by
      change AspisR1Post25Sampler.sampler.low_base_p_digits block = .ok (lowDigits, q)
      exact hlow
    have hadd1' : candidateGammaHelpers.add lowDigits n =
        .ok (carry1 != 0#u32, digits1) := by
      change AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p
        lowDigits n = .ok (carry1 != 0#u32, digits1)
      exact hadd1
    have hadd2' : candidateGammaHelpers.add digits1 1#u32 =
        .ok (carry2 != 0#u32, digits2) := by
      change AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p
        digits1 1#u32 = .ok (carry2 != 0#u32, digits2)
      exact hadd2
    refine ⟨out, ?_⟩
    unfold AspisR1GammaCaller.sampler.gamma_sample
    rw [hlow']
    rw [bind_pair_ok]
    rw [hn]
    simp only [bind_tc_ok]
    rw [hadd1']
    rw [bind_pair_ok]
    rw [hbool]
    rw [if_pos rfl]
    rw [hadd2']
    rw [bind_pair_ok]
    simp only [bind_tc_ok, hdecode]


#print axioms candidate_gamma_total

end AspisR1GammaCaller.DigitsModel
