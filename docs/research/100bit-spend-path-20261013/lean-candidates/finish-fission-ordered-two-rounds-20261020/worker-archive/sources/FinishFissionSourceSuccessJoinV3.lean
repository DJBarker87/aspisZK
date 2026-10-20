import FinishFissionHelperLoopV2
import FinishCandidateOuterSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishFissionSourceSuccessJoin
open _root_.AspisR1FinishRelationCurrent

open AspisR1FinishFissionProof
open AspisR1FinishFissionHelperAdapterV2

private def alpha0Entry (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[0]'(by
    have hlen : (0#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

private def alpha1Entry (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[1]'(by
    have hlen : (1#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

def environmentOf (v : verifier.View) (p : verifier.Prepared) : RoundEnvironment :=
  { v := v, v1 := v.variant, inactive := v.inactive, foldedRoot := v.folded_root,
    v2 := p.variant, roots := p.roots, gamma := p.gamma, kappa := p.kappa,
    alpha := p.alpha, rho := p.rho, queries := p.queries,
    semanticAlpha := p.semantic_alpha, z := p.z, preparedClaim := p.claim,
    state := p.state }

theorem environmentOf_view (v : verifier.View) (p : verifier.Prepared) :
    assembledView (environmentOf v p) = v := by
  cases v
  rfl

theorem environmentOf_prepared (v : verifier.View) (p : verifier.Prepared) :
    assembledPrepared (environmentOf v p) = p := by
  cases p
  rfl

theorem s2_success_fission_model
    {W D : Type}
    (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit))
    (hv : p.variant = transport.Variant.S2)
    (hfinish : verifier.finish_relation ops v p a obs = .ok (.Ok ()))
    (i0 i1 i2 : Range)
    (hround0 : i0.start = 0#usize) (hround1 : i1.start = 1#usize)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hnext1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i1 =
      .ok (some i1.start, i2))
    (hnext2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i2 =
      .ok (none, i2)) :
    ∃ alpha0 claim1 alpha1 claim2,
      Array.index_usize p.alpha 0#usize = .ok alpha0 ∧
      Array.index_usize p.alpha 1#usize = .ok alpha1 ∧
      loopAdapter
        (fun vv pp claim round => AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops vv pp claim round)
        (environmentOf v p) i0 p.claim = .ok (claim2, none) ∧
      FinishCandidateEquations.RoundEquation ops v.round0 (alpha0Entry p) p.claim claim1 ∧
      FinishCandidateEquations.RoundEquation ops v.round1 (alpha1Entry p) claim1 claim2 := by
  obtain ⟨alpha0, claim1, alpha1, claim2, w, sliced, pair, actual,
      h0, hr0, h1, hr1, hw, hs, hp, hpair, hmark, hd, hnext, hdot, hfinal⟩ :=
    FinishCandidateOuterSuccess.s2_success_calls ops v p a obs hv hfinish
  have hpSel0 :
      AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel v 0#usize =
        .ok v.round0 := by
    unfold AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel
    simp
  have hpSel1 :
      AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel v 1#usize =
        .ok v.round1 := by
    unfold AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel
    have hneq : (1#usize : Usize) ≠ 0#usize := by scalar_tac
    simp [hneq]
  have hstep0 :
      capturedStep (fun vv pp claim round => AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops vv pp claim round)
        (environmentOf v p) i0.start p.claim = .ok (.Ok claim1) := by
    rw [hround0]
    change AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops (assembledView (environmentOf v p))
      (assembledPrepared (environmentOf v p)) p.claim 0#usize = .ok (.Ok claim1)
    rw [environmentOf_view, environmentOf_prepared]
    have hbridge0 :
        AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops v p p.claim 0#usize =
          verifier.finish_relation_round ops v.round0 alpha0 p.claim 0#usize := by
      simp only [AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter,
        hpSel0, AspisR1FinishFissionHelperAdapterV2.selectRoundAlphaModel,
        h0, bind_tc_ok, verifier.finish_relation_round]
    rw [hbridge0]
    exact hr0
  have hstep1 :
      capturedStep (fun vv pp claim round => AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops vv pp claim round)
        (environmentOf v p) i1.start claim1 = .ok (.Ok claim2) := by
    rw [hround1]
    change AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops (assembledView (environmentOf v p))
      (assembledPrepared (environmentOf v p)) claim1 1#usize = .ok (.Ok claim2)
    rw [environmentOf_view, environmentOf_prepared]
    have hbridge1 :
        AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops v p claim1 1#usize =
          verifier.finish_relation_round ops v.round1 alpha1 claim1 1#usize := by
      simp only [AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter,
        hpSel1, AspisR1FinishFissionHelperAdapterV2.selectRoundAlphaModel,
        h1, bind_tc_ok, verifier.finish_relation_round]
    rw [hbridge1]
    exact hr1
  have hlo := AspisR1FinishFissionHelperLoop.fission_loop_two_rounds_with_helper
    ops faithful (environmentOf v p) i0 i1 i2 p.claim claim1 claim2
    hround0 hround1 hnext0 hnext1 hnext2 hstep0 hstep1
  rcases hlo with ⟨hloop, heq0, heq1⟩
  rw [environmentOf_prepared, environmentOf_view] at heq0 heq1
  exact ⟨alpha0, claim1, alpha1, claim2, h0, h1, hloop, heq0, heq1⟩

#print axioms s2_success_fission_model
end AspisR1FinishFissionSourceSuccessJoin
