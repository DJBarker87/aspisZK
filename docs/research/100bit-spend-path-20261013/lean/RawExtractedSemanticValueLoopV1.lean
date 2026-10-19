import AspisR1SemanticCallExtraction.Funs
import RawExtractedSemanticCallOpsV23
import RawSemanticPolynomialOps

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23
open AspisR1.ExtractedMaskQM31Exact

abbrev GenQ := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev ExactQ := AspisR1.ExtractedMaskQM31Exact.QM31Exact

def coefficients (p : Array GenQ 28#usize) : List ExactQ :=
  p.val.map (fun x => decode (genQToProbe x))

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem generated_zero_canonical :
    Canonical (genQToProbe AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO) := by
  simp [Canonical, AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
    genQToProbe, genCToProbe,
    AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO,
    AspisR1SelectedMaskProbe.field.QM31.ZERO,
    AspisR1.ExtractedMaskTowerAdd.P,
    AspisR1.ExtractedMaskM31AddSub.P]

private theorem generated_zero_decode :
    decode (genQToProbe AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO) = 0 := by
  ext <;> simp [decode, genQToProbe, genCToProbe,
    AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO]

private theorem sourceValue_cons (x c : ExactQ) (cs : List ExactQ) :
    AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue x (c :: cs) =
      AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue x cs * x + c := by
  rw [AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue_eq_lowHorner]
  change AspisR1PublicPreparation.RawSemanticPolynomialOps.lowHorner x (c :: cs) = _
  rw [show AspisR1PublicPreparation.RawSemanticPolynomialOps.lowHorner x (c :: cs) =
    c + x * AspisR1PublicPreparation.RawSemanticPolynomialOps.lowHorner x cs by rfl]
  rw [← AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue_eq_lowHorner]
  rw [mul_comm x (AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue x cs), add_comm]

theorem semantic_value_loop_refines
    (p : Array GenQ 28#usize) (alpha : Array GenQ 10#usize) (round : Usize)
    (hround : round.val < 10)
    (halpha : Canonical (genQToProbe (alpha.val[round.val]'(by
      simpa [alpha.property] using hround))))
    (hp : ∀ i : Nat, (hi : i < 28) →
      Canonical (genQToProbe (p.val[i]'(by simpa [p.property] using hi)))) :
    ∃ out : GenQ,
      AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop
        p alpha round 28#usize
        AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO = .ok out ∧
      Canonical (genQToProbe out) ∧
      decode (genQToProbe out) =
        AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
          (decode (genQToProbe (alpha.val[round.val]'(by
            simpa [alpha.property] using hround)))) (coefficients p) := by
  have hs : WP.spec
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop p alpha round
        28#usize AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO)
      (fun out : GenQ => Canonical (genQToProbe out) ∧
        decode (genQToProbe out) =
          AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
            (decode (genQToProbe (alpha.val[round.val]'(by
              simpa [alpha.property] using hround)))) (coefficients p)) := by
    unfold AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop
    refine loop.spec_decr_nat
      (fun s : Usize × GenQ => s.1.val)
      (fun s => s.1.val ≤ 28 ∧ Canonical (genQToProbe s.2) ∧
        decode (genQToProbe s.2) =
          AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
            (decode (genQToProbe (alpha.val[round.val]'(by
              simpa [alpha.property] using hround)))) ((coefficients p).drop s.1.val))
      (fun out : GenQ => Canonical (genQToProbe out) ∧
        decode (genQToProbe out) =
          AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
            (decode (genQToProbe (alpha.val[round.val]'(by
              simpa [alpha.property] using hround)))) (coefficients p))
      (fun s : Usize × GenQ =>
        AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body p alpha round s.1 s.2)
      (28#usize, AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO) ?_
      ⟨by change (28#usize).val ≤ 28; decide,
       generated_zero_canonical,
       by change decode (genQToProbe AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO) = _
          ; rw [generated_zero_decode]
          ; simp [coefficients, AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue]⟩
    rintro ⟨idx, value⟩ ⟨hidxbound, hvaluecanonical, hvalue⟩
    change idx.val ≤ 28 at hidxbound
    change Canonical (genQToProbe value) at hvaluecanonical
    change decode (genQToProbe value) =
      AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
        (decode (genQToProbe (alpha.val[round.val]'(by
          simpa [alpha.property] using hround)))) ((coefficients p).drop idx.val) at hvalue
    by_cases hi : 0 < idx.val
    · have hguard : idx > 0#usize := by
        change 0 < idx.val
        exact hi
      have hone : (1#usize).val = 1 := by decide
      have hsubSpec : UScalar.sub idx 1#usize ⦃ z => z.val = idx.val - 1 ∧ 1 ≤ idx.val ⦄ := by
        apply UScalar.sub_spec
        rw [hone]
        omega
      obtain ⟨idx', hsub, hidxpost⟩ := WP.spec_imp_exists hsubSpec
      have hidxval := hidxpost.1
      have hidxval' : idx'.val + 1 = idx.val := by omega
      have hidxlt : idx.val - 1 < 28 := by omega
      let coeff : GenQ := p.val[(idx.val - 1)]'(by simpa [p.property] using hidxlt)
      have hreadCoeff : Array.index_usize p idx' = .ok coeff := by
        have hidx' : idx'.val = idx.val - 1 := by omega
        have hb : idx'.val < (28#usize).val := by rw [hidx']; simpa using hidxlt
        simpa [coeff, hidx'] using array_index_usize_ok p idx' hb
      have hreadAlpha : Array.index_usize alpha round =
          .ok (alpha.val[round.val]'(by simpa [alpha.property] using hround)) :=
        array_index_usize_ok alpha round (by simpa [alpha.property] using hround)
      obtain ⟨product, hmul, hproductcanonical, hproductdecode⟩ :=
        generated_qm_mul_exact value (alpha.val[round.val]'(by
          simpa [alpha.property] using hround)) hvaluecanonical halpha
      have hcoeffcanonical : Canonical (genQToProbe coeff) := by
        exact hp (idx.val - 1) hidxlt
      obtain ⟨value', hadd, hvalue'canonical, hadddecode⟩ :=
        generated_qm_add_exact product coeff hproductcanonical hcoeffcanonical
      have hdrop : (coefficients p).drop (idx.val - 1) =
          (coefficients p)[idx.val - 1]'(by simp [coefficients, p.property]; omega) ::
            (coefficients p).drop idx.val := by
        rw [List.drop_eq_getElem_cons (by simp [coefficients, p.property]; omega)]
        have hn : idx.val - 1 + 1 = idx.val := by omega
        rw [hn]
      have hcoeffdecode : (coefficients p)[idx.val - 1]'(by
          simp [coefficients, p.property]
          omega) = decode (genQToProbe coeff) := by
        simp [coefficients, coeff]
      have hsubNat : idx'.val = idx.val - 1 := by omega
      have hsubExpr : idx - 1#usize = Result.ok idx' := by
        change HSub.hSub idx 1#usize = Result.ok idx'
        exact hsub
      simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body,
        if_pos hguard, hsubExpr, bind_tc_ok, hreadAlpha, bind_tc_ok, hmul,
        bind_tc_ok, hreadCoeff, bind_tc_ok, hadd, bind_tc_ok]
      rw [WP.spec_ok]
      change ((idx'.val ≤ 28 ∧ Canonical (genQToProbe value') ∧
        decode (genQToProbe value') =
          AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
            (decode (genQToProbe (alpha.val[round.val]'(by
              simpa [alpha.property] using hround)))) ((coefficients p).drop idx'.val)) ∧
        idx'.val < idx.val)
      refine ⟨⟨by omega, hvalue'canonical, ?_⟩, by omega⟩
      rw [hsubNat, hadddecode, hproductdecode, hvalue, hdrop, hcoeffdecode]
      exact (sourceValue_cons _ _ _).symm
    · have hguard : ¬ idx > 0#usize := by
        change ¬ 0 < idx.val
        omega
      have heq : idx.val = 0 := by omega
      simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body,
        hguard, if_false]
      rw [WP.spec_ok]
      change Canonical (genQToProbe value) ∧
        decode (genQToProbe value) =
          AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
            (decode (genQToProbe (alpha.val[round.val]'(by
              simpa [alpha.property] using hround)))) (coefficients p)
      exact ⟨hvaluecanonical, by simpa [heq] using hvalue⟩
  obtain ⟨out, hout, hprop⟩ := WP.spec_imp_exists hs
  exact ⟨out, hout, hprop.1, hprop.2⟩

theorem semantic_value_refines_polynomial_eval
    (p : Array GenQ 28#usize) (alpha : Array GenQ 10#usize) (round : Usize)
    (hround : round.val < 10)
    (halpha : Canonical (genQToProbe (alpha.val[round.val]'(by
      simpa [alpha.property] using hround))))
    (hp : ∀ i : Nat, (hi : i < 28) →
      Canonical (genQToProbe (p.val[i]'(by simpa [p.property] using hi)))) :
    ∃ out : GenQ,
      AspisR1SemanticCallExtraction.r1_semantic.semantic_value p alpha round = .ok out ∧
      Canonical (genQToProbe out) ∧
      decode (genQToProbe out) =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial (coefficients p)).eval
          (decode (genQToProbe (alpha.val[round.val]'(by
            simpa [alpha.property] using hround)))) := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ := semantic_value_loop_refines p alpha round hround halpha hp
  refine ⟨out, ?_, hcanonical, ?_⟩
  · simpa [AspisR1SemanticCallExtraction.r1_semantic.semantic_value] using hout
  · exact hvalue.trans (AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue_eq_polynomial_eval
      _ (coefficients p))

#print axioms semantic_value_loop_refines
#print axioms semantic_value_refines_polynomial_eval
end AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1
