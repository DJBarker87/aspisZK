import AeneasOriginalPolynomialFinishBridgeV1
import FinishFissionCurrentNumericV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FinishFissionOriginalNumericV1

open _root_.AspisR1FinishRelationCurrent

abbrev FinishOps := _root_.AspisR1FinishRelationCurrent.FinishOps

 theorem s2_original_success_fission_current_numeric
    {W D : Type}
    (baseOps : FinishOps W D)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit))
    (hv : p.variant = transport.Variant.S2)
    (hclaim : AspisR1CurrentWide.Proof.CanonicalFinish p.claim)
    (halpha0 : ∀ x, Array.index_usize p.alpha 0#usize = .ok x → AspisR1CurrentWide.Proof.CanonicalFinish x)
    (halpha1 : ∀ x, Array.index_usize p.alpha 1#usize = .ok x → AspisR1CurrentWide.Proof.CanonicalFinish x)
    (hfinish : verifier.finish_relation
      (AspisR1CurrentWide.OriginalPolynomialFinishBridge.finishOriginalPolynomialOps baseOps)
      v p a obs = .ok (.Ok ())) :
    ∃ alpha0 claim1 alpha1 claim2,
      Array.index_usize p.alpha 0#usize = .ok alpha0 ∧
      AspisR1CurrentWide.Proof.CanonicalFinish claim1 ∧
      AspisR1CurrentWide.Proof.FinishPolynomialEvaluation v.round0 alpha0 claim1 ∧
      (∃ x0 x4, AspisR1CurrentWide.Proof.finishField v.round0 0#usize = .ok x0 ∧
        AspisR1CurrentWide.Proof.finishField v.round0 4#usize = .ok x4 ∧
        AspisR1CurrentWide.Proof.decodeFinish x0 + AspisR1CurrentWide.Proof.decodeFinish x4 =
          AspisR1CurrentWide.Proof.decodeFinish p.claim * (536870912 : AspisWideTower.WideExact)) ∧
      Array.index_usize p.alpha 1#usize = .ok alpha1 ∧
      AspisR1CurrentWide.Proof.CanonicalFinish claim2 ∧
      AspisR1CurrentWide.Proof.FinishPolynomialEvaluation v.round1 alpha1 claim2 ∧
      (∃ x0 x4, AspisR1CurrentWide.Proof.finishField v.round1 0#usize = .ok x0 ∧
        AspisR1CurrentWide.Proof.finishField v.round1 4#usize = .ok x4 ∧
        AspisR1CurrentWide.Proof.decodeFinish x0 + AspisR1CurrentWide.Proof.decodeFinish x4 =
          AspisR1CurrentWide.Proof.decodeFinish claim1 * (536870912 : AspisWideTower.WideExact)) ∧
      AspisR1FinishFissionProof.loopAdapter
        (fun vv pp claim round =>
          AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter
            (AspisR1CurrentWide.Proof.finishUnrolledPolynomialOps baseOps) vv pp claim round)
        (AspisR1FinishFissionSourceSuccessJoin.environmentOf v p)
        AspisR1FinishFissionLiteralRange.range0 p.claim = .ok (claim2, none) := by
  have hUnrolled : verifier.finish_relation
      (AspisR1CurrentWide.Proof.finishUnrolledPolynomialOps baseOps) v p a obs = .ok (.Ok ()) := by
    rw [← AspisR1CurrentWide.OriginalPolynomialFinishBridge.finish_relation_original_ops_eq_unrolled
      baseOps v p a obs]
    exact hfinish
  exact AspisR1FinishFissionCurrentNumericV1.s2_success_fission_current_numeric
    baseOps v p a obs hv hclaim halpha0 halpha1 hUnrolled

#print axioms s2_original_success_fission_current_numeric
end AspisR1FinishFissionOriginalNumericV1
