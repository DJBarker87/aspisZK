import FinishFissionLiteralRangeV1
import CurrentFinishPolynomialNumericEquations

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FinishFissionCurrentNumericV1
open _root_.AspisR1FinishRelationCurrent
open AspisR1FinishFissionProof
open AspisR1CurrentWide.Proof

theorem s2_success_fission_current_numeric
    {W D : Type}
    (baseOps : _root_.AspisR1FinishRelationCurrent.FinishOps W D)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit))
    (hv : p.variant = transport.Variant.S2)
    (hclaim : CanonicalFinish p.claim)
    (halpha0 : ∀ x, Array.index_usize p.alpha 0#usize = .ok x → CanonicalFinish x)
    (halpha1 : ∀ x, Array.index_usize p.alpha 1#usize = .ok x → CanonicalFinish x)
    (hfinish : verifier.finish_relation (finishUnrolledPolynomialOps baseOps)
      v p a obs = .ok (.Ok ())) :
    ∃ alpha0 claim1 alpha1 claim2,
      Array.index_usize p.alpha 0#usize = .ok alpha0 ∧
      CanonicalFinish claim1 ∧
      FinishPolynomialEvaluation v.round0 alpha0 claim1 ∧
      (∃ x0 x4, finishField v.round0 0#usize = .ok x0 ∧
        finishField v.round0 4#usize = .ok x4 ∧
        decodeFinish x0 + decodeFinish x4 =
          decodeFinish p.claim * (536870912 : AspisWideTower.WideExact)) ∧
      Array.index_usize p.alpha 1#usize = .ok alpha1 ∧
      CanonicalFinish claim2 ∧
      FinishPolynomialEvaluation v.round1 alpha1 claim2 ∧
      (∃ x0 x4, finishField v.round1 0#usize = .ok x0 ∧
        finishField v.round1 4#usize = .ok x4 ∧
        decodeFinish x0 + decodeFinish x4 =
          decodeFinish claim1 * (536870912 : AspisWideTower.WideExact)) ∧
      loopAdapter
        (fun vv pp claim round =>
          AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter
            (finishUnrolledPolynomialOps baseOps) vv pp claim round)
        (AspisR1FinishFissionSourceSuccessJoin.environmentOf v p)
        (AspisR1FinishFissionLiteralRange.range0) p.claim = .ok (claim2, none) := by
  let cop := finishUnrolledPolynomialOps baseOps
  have hfaith : ∀ x y, cop.eq x y = .ok true → x = y := by
    intro x y he
    exact finish_eq_success_true x y (by
      simpa [cop, finishUnrolledPolynomialOps, finishConcreteField,
        finishCheckedArithmetic, finishEq] using he)
  obtain ⟨alpha0, claim1, alpha1, claim2, hidx0, hidx1, hloop, hr0, hr1⟩ :=
    AspisR1FinishFissionLiteralRange.s2_success_fission_model_no_range_hypotheses
      cop hfaith v p a obs hv (by simpa [cop] using hfinish)
  have hslot0 := AspisR1FinishRoundAlphaSemantic.alpha_at_zero p alpha0 hidx0
  have hslot1 := AspisR1FinishRoundAlphaSemantic.alpha_at_one p alpha1 hidx1
  change FinishCandidateEquations.RoundEquation cop v.round0
    (p.alpha.val[0]'(by
      have hlen : (0#usize).val < (2#usize).val := by scalar_tac
      simpa [p.alpha.property] using hlen)) p.claim claim1 at hr0
  change FinishCandidateEquations.RoundEquation cop v.round1
    (p.alpha.val[1]'(by
      have hlen : (1#usize).val < (2#usize).val := by scalar_tac
      simpa [p.alpha.property] using hlen)) claim1 claim2 at hr1
  rw [hslot0.symm] at hr0
  rw [hslot1.symm] at hr1
  have hc1 : CanonicalFinish claim1 ∧
      FinishPolynomialEvaluation v.round0 alpha0 claim1 := by
    rcases hr0 with ⟨_,_,_,_,_,_,_,_,_,_,_,hpoly⟩
    have hpoly' : finishUnrolledPolynomial v.round0 alpha0 = .ok claim1 := by
      simpa [cop, finishUnrolledPolynomialOps] using hpoly
    exact finish_unrolled_polynomial_success_evaluation v.round0 alpha0 claim1
      (halpha0 alpha0 hidx0) hpoly'
  have hr0' : FinishCandidateEquations.RoundEquation
      (finishArithmetic cop) v.round0 alpha0 p.claim claim1 := by
    change FinishCandidateEquations.RoundEquation cop v.round0 alpha0 p.claim claim1 at hr0
    exact hr0
  have hn0 := current_round_equation cop v.round0 alpha0 p.claim claim1 hclaim
    (finishField_success_canonical v.round0 0#usize)
    (finishField_success_canonical v.round0 4#usize) hr0'
  have hc2 : CanonicalFinish claim2 ∧
      FinishPolynomialEvaluation v.round1 alpha1 claim2 := by
    rcases hr1 with ⟨_,_,_,_,_,_,_,_,_,_,_,hpoly⟩
    have hpoly' : finishUnrolledPolynomial v.round1 alpha1 = .ok claim2 := by
      simpa [cop, finishUnrolledPolynomialOps] using hpoly
    exact finish_unrolled_polynomial_success_evaluation v.round1 alpha1 claim2
      (halpha1 alpha1 hidx1) hpoly'
  have hr1' : FinishCandidateEquations.RoundEquation
      (finishArithmetic cop) v.round1 alpha1 claim1 claim2 := by
    change FinishCandidateEquations.RoundEquation cop v.round1 alpha1 claim1 claim2 at hr1
    exact hr1
  have hn1 := current_round_equation cop v.round1 alpha1 claim1 claim2 hc1.1
    (finishField_success_canonical v.round1 0#usize)
    (finishField_success_canonical v.round1 4#usize) hr1'
  exact ⟨alpha0,claim1,alpha1,claim2,hidx0,hc1.1,hc1.2,hn0,
    hidx1,hc2.1,hc2.2,hn1,hloop⟩

#print axioms s2_success_fission_current_numeric
end AspisR1FinishFissionCurrentNumericV1
