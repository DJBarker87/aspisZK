import GammaCandidateAddSmallHelpersRefine
import IndexedCandidateDecode8RetainedBridgeV3

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace AspisR1GammaCaller.DigitsModel

open AspisR1
open AspisR1.SamplerMachineBounds
open AspisR1.SourceSamplerByteRank
open AspisR1.SamplerAddDigits
open AspisR1.SamplerNatModel
open AspisR1.SamplerRanking
open AspisWideTower

private abbrev SP : Nat := AspisR1.SamplerMachineBounds.P
private abbrev EP : Nat := AspisV8R15.ExactTowerBase.P

private theorem samplerP_eq_circleP : SP = AspisCircleGroupOrder.P := rfl
private theorem samplerP_eq_exactP : SP = EP := rfl

abbrev GammaDigits := Array U32 8#usize
abbrev GammaWide := AspisR1GammaCaller.field.WideExact
abbrev DecodedWide := AspisR1Post25Sampler.field.WideExact

private def digitAt (digits : GammaDigits) (i : Fin 8) : U32 :=
  digits.val[i.val]'(by simpa [digits.property] using i.isLt)

private def decodedWideToGamma (v : DecodedWide) : GammaWide :=
  ⟨⟨⟨v.c0.c0.a, v.c0.c0.b⟩, ⟨v.c0.c1.a, v.c0.c1.b⟩⟩,
    ⟨⟨v.c1.c0.a, v.c1.c0.b⟩, ⟨v.c1.c1.a, v.c1.c1.b⟩⟩⟩

def gammaWideToExact (v : GammaWide) : WideExact :=
  ⟨⟨⟨(v.c0.c0.a.val : AspisV8R15.ExactTowerBase.M31Exact),
        (v.c0.c0.b.val : AspisV8R15.ExactTowerBase.M31Exact)⟩,
    ⟨(v.c0.c1.a.val : AspisV8R15.ExactTowerBase.M31Exact),
      (v.c0.c1.b.val : AspisV8R15.ExactTowerBase.M31Exact)⟩⟩,
    ⟨⟨(v.c1.c0.a.val : AspisV8R15.ExactTowerBase.M31Exact),
        (v.c1.c0.b.val : AspisV8R15.ExactTowerBase.M31Exact)⟩,
      ⟨(v.c1.c1.a.val : AspisV8R15.ExactTowerBase.M31Exact),
        (v.c1.c1.b.val : AspisV8R15.ExactTowerBase.M31Exact)⟩⟩⟩

private theorem decoded_gamma_exact_eq (v : DecodedWide) :
    gammaWideToExact (decodedWideToGamma v) =
      AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.candidateWideToExact v := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl

private def candidateDecode (digits : GammaDigits) : Result GammaWide := do
  let value ← AspisR1Post25Sampler.sampler.decode8 digits
  .ok (decodedWideToGamma value)

def candidateGammaHelpers : GammaHelpers where
  low := fun block => AspisR1Post25Sampler.sampler.low_base_p_digits block
  add := fun ds n => AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p ds n
  decode := candidateDecode

private theorem gamma_canonical_to_fin (digits : GammaDigits)
    (hcanonical : Canonical digits) :
    ∀ i : Fin 8,
      (digitAt digits i).val < AspisV8R15.ExactTowerBase.P := by
  intro i
  have hmem : (digitAt digits i).val ∈ values digits := by
    unfold digitAt values
    rw [List.mem_map]
    exact ⟨digits.val[i.val]'(by simpa [digits.property] using i.isLt),
      List.getElem_mem _, rfl⟩
  have h := hcanonical _ hmem
  change (digitAt digits i).val < 2147483647 at h
  change (digitAt digits i).val < 2147483647
  exact h

private theorem digitsValue_fin_sum (p : Nat) (xs : List Nat) :
    digitsValue p xs =
      ∑ i : Fin xs.length, xs[i.val]'i.isLt * p ^ i.val := by
  induction xs with
  | nil => simp [digitsValue]
  | cons d ds ih =>
      calc
        digitsValue p (d :: ds) = d + p * digitsValue p ds := rfl
        _ = d + p * (∑ i : Fin ds.length, ds[i.val]'i.isLt * p ^ i.val) := by rw [ih]
        _ = d + ∑ i : Fin ds.length, ds[i.val]'i.isLt * p ^ (i.val + 1) := by
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring
        _ = ∑ i : Fin (ds.length + 1), (d :: ds)[i.val]'i.isLt * p ^ i.val := by
          rw [Fin.sum_univ_succ]
          simp only [List.getElem_cons_zero, List.getElem_cons_succ,
            Fin.val_zero, Fin.val_succ, pow_zero, Nat.mul_one]

private theorem candidate_digits_fieldRank (digits : GammaDigits)
    (scalar : Nat)
    (hcanonical : ∀ i : Fin 8,
      (digitAt digits i).val < AspisV8R15.ExactTowerBase.P)
    (hvalue : digitsValue EP (values digits) = scalar)
    (hscalar : scalar < EP ^ 8) :
    R0C.ModuloField.digitsField
        (AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.retainedDigits
          digits hcanonical) =
      R0C.ModuloField.fieldRank ⟨scalar, by
        change scalar < AspisCircleGroupOrder.P ^ 8
        have heq : EP = AspisCircleGroupOrder.P :=
          samplerP_eq_exactP.symm.trans samplerP_eq_circleP
        rw [← heq]
        exact hscalar⟩ := by
  let f := AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.retainedDigits
    digits hcanonical
  have hlen : (values digits).length = 8 := by
    simp only [values, List.length_map]
    have hdigits := digits.property
    change digits.val.length = (8#usize).val at hdigits
    have h8 : (8#usize).val = 8 := by decide
    omega
  have hfval : ∀ i : Fin 8, (f i).val =
      (values digits)[i.val]'(by
        simp only [values, List.length_map]
        have hlen := digits.property
        change digits.val.length = (8#usize).val at hlen
        have h8 : (8#usize).val = 8 := by decide
        omega) := by
    intro i
    unfold f
    change (digits.val[i.val]'(by simpa [digits.property] using i.isLt)).val =
      (values digits)[i.val]'(by simpa [hlen] using i.isLt)
    simp only [values, List.getElem_map]
  have hpos :
      (SamplerRanking.digitsRank EP 8 f).val = digitsValue EP (values digits) := by
    rw [SamplerRanking.digitsRank_value]
    have hsum0 := digitsValue_fin_sum EP (values digits)
    have hsum : digitsValue EP (values digits) =
        ∑ i : Fin 8, (values digits)[i.val]'(by
          simp only [values, List.length_map]
          have hlen' := digits.property
          change digits.val.length = (8#usize).val at hlen'
          have h8 : (8#usize).val = 8 := by decide
          omega) * EP ^ i.val := by
      let e : Fin 8 ≃ Fin (values digits).length := finCongr hlen.symm
      let term : Fin (values digits).length → Nat := fun i =>
        (values digits)[i.val]'i.isLt * EP ^ i.val
      calc
        digitsValue EP (values digits) = ∑ i : Fin (values digits).length,
            (values digits)[i.val]'i.isLt * EP ^ i.val := by
          exact hsum0
        _ = ∑ i : Fin 8, term (e i) := (Equiv.sum_comp e term).symm
        _ = ∑ i : Fin 8, (values digits)[i.val]'(by
              simp only [values, List.length_map]
              have hlen' := digits.property
              change digits.val.length = (8#usize).val at hlen'
              have h8 : (8#usize).val = 8 := by decide
              omega) * EP ^ i.val := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [term, e, hlen]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfval i]
  have hscalarCircle : scalar < AspisCircleGroupOrder.P ^ 8 := by
    have heq : EP = AspisCircleGroupOrder.P :=
      samplerP_eq_exactP.symm.trans samplerP_eq_circleP
    rw [← heq]
    exact hscalar
  have hfin : SamplerRanking.digitsRank EP 8 f = ⟨scalar, hscalarCircle⟩ := by
    apply Fin.ext
    simpa [hvalue] using hpos
  have hsymm : f = (SamplerRanking.digitsRank EP 8).symm ⟨scalar, hscalarCircle⟩ := by
    calc
      f = (SamplerRanking.digitsRank EP 8).symm (SamplerRanking.digitsRank EP 8 f) := by
        rw [Equiv.symm_apply_apply]
      _ = (SamplerRanking.digitsRank EP 8).symm ⟨scalar, hscalarCircle⟩ := by
        rw [hfin]
  change R0C.ModuloField.digitsField f =
    R0C.ModuloField.digitsField ((SamplerRanking.digitsRank EP 8).symm ⟨scalar, hscalarCircle⟩)
  exact congrArg R0C.ModuloField.digitsField hsymm

theorem candidate_gamma_decode_fieldRank (block : CandidateBytes32)
    (out : GammaWide)
    (h : AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block = .ok out) :
    ∃ digits : GammaDigits,
      candidateDecode digits = .ok out ∧
      Canonical digits ∧
      digitsValue SP (values digits) = rank block % (SP ^ 8 - 1) + 1 ∧
      gammaWideToExact out = R0C.ModuloField.fieldRank ⟨
        rank block % (SP ^ 8 - 1) + 1, by
          change rank block % (AspisCircleGroupOrder.P ^ 8 - 1) + 1 <
            AspisCircleGroupOrder.P ^ 8
          have hb := (SamplerNatModel.gammaDigits_value_bounds (rank_lt block)).2
          rw [SamplerNatModel.gammaDigits_value (rank_lt block)] at hb
          simpa [samplerP_eq_circleP] using hb⟩ := by
  obtain ⟨digits, hdecode, hcanonical, hvalue, hpos, hbound⟩ :=
    candidate_gamma_rank_success candidateDecode block out h
  have hdecodeOrig := hdecode
  have hcanonicalFin := gamma_canonical_to_fin digits hcanonical
  unfold candidateDecode at hdecode
  cases h8 : AspisR1Post25Sampler.sampler.decode8 digits with
  | ok decoded =>
      simp only [h8, bind_tc_ok] at hdecode
      have hout : decodedWideToGamma decoded = out := Result.ok.inj hdecode
      obtain ⟨decoded', hdecoded', hretained⟩ :=
        AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.decode8_candidate_eq_retained
          digits hcanonicalFin
      have heq : decoded' = decoded := Result.ok.inj (hdecoded'.symm.trans h8)
      subst decoded'
      have hvalueEP : digitsValue EP (values digits) =
          rank block % (SP ^ 8 - 1) + 1 := by
        simpa [samplerP_eq_exactP] using hvalue
      have hboundEP : rank block % (SP ^ 8 - 1) + 1 < EP ^ 8 := by
        have hb : digitsValue EP (values digits) < EP ^ 8 := by
          simpa [samplerP_eq_exactP] using hbound
        rw [← hvalueEP]
        exact hb
      have hfield := candidate_digits_fieldRank digits
        (rank block % (SP ^ 8 - 1) + 1) hcanonicalFin hvalueEP hboundEP
      refine ⟨digits, hdecodeOrig, hcanonical, hvalue, ?_⟩
      · calc
          gammaWideToExact out =
              gammaWideToExact (decodedWideToGamma decoded) := by rw [hout]
          _ = AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.candidateWideToExact decoded :=
            decoded_gamma_exact_eq decoded
          _ = R0C.ModuloField.digitsField
              (AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.retainedDigits
                digits hcanonicalFin) := hretained
          _ = R0C.ModuloField.fieldRank ⟨rank block % (SP ^ 8 - 1) + 1, by
                change rank block % (AspisCircleGroupOrder.P ^ 8 - 1) + 1 <
                  AspisCircleGroupOrder.P ^ 8
                have hb := (SamplerNatModel.gammaDigits_value_bounds (rank_lt block)).2
                rw [SamplerNatModel.gammaDigits_value (rank_lt block)] at hb
                simpa [samplerP_eq_circleP] using hb⟩ := hfield
  | fail err =>
      simp only [h8, bind_tc_fail] at hdecode
      cases hdecode
  | div =>
      simp only [h8, bind_tc_div] at hdecode
      cases hdecode

#print axioms candidate_gamma_decode_fieldRank

end AspisR1GammaCaller.DigitsModel
