import FissionLoopStepSemanticsV1
import FinishFissionHelperAdapterV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishFissionHelperLoop
open _root_.AspisR1FinishRelationCurrent

private def alpha0Entry (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[0]'(by
    have hlen : (0#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

private def alpha1Entry (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[1]'(by
    have hlen : (1#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

theorem fission_loop_two_rounds_with_helper
    {W D : Type}
    (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (env : AspisR1FinishFissionProof.RoundEnvironment)
    (i0 i1 i2 : AspisR1FinishFissionProof.Range)
    (c0 c1 c2 : aspis_core.field.WideExact)
    (hround0 : i0.start = 0#usize) (hround1 : i1.start = 1#usize)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hnext1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i1 =
      .ok (some i1.start, i2))
    (hnext2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i2 =
      .ok (none, i2))
    (hstep0 : AspisR1FinishFissionProof.capturedStep
      (fun v p claim round =>
        AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops v p claim round)
      env i0.start c0 = .ok (.Ok c1))
    (hstep1 : AspisR1FinishFissionProof.capturedStep
      (fun v p claim round =>
        AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops v p claim round)
      env i1.start c1 = .ok (.Ok c2)) :
    AspisR1FinishFissionProof.loopAdapter
      (fun v p claim round =>
        AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops v p claim round)
      env i0 c0 = .ok (c2, none) ∧
    FinishCandidateEquations.RoundEquation ops
      (AspisR1FinishFissionProof.assembledView env).round0
      (alpha0Entry (AspisR1FinishFissionProof.assembledPrepared env)) c0 c1 ∧
    FinishCandidateEquations.RoundEquation ops
      (AspisR1FinishFissionProof.assembledView env).round1
      (alpha1Entry (AspisR1FinishFissionProof.assembledPrepared env)) c1 c2 := by
  have hzero := AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter_zero_equation
    ops faithful (AspisR1FinishFissionProof.assembledView env)
    (AspisR1FinishFissionProof.assembledPrepared env) c0 c1 (by
      simpa [AspisR1FinishFissionProof.capturedStep, hround0] using hstep0)
  have hone := AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter_one_equation
    ops faithful (AspisR1FinishFissionProof.assembledView env)
    (AspisR1FinishFissionProof.assembledPrepared env) c1 c2 (by
      simpa [AspisR1FinishFissionProof.capturedStep, hround1] using hstep1)
  have hlo := AspisR1FinishFissionProof.loopAdapter_two_rounds
    (fun v p claim round =>
      AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops v p claim round)
    env i0 i1 i2 c0 c1 c2 hnext0 hnext1 hnext2 hstep0 hstep1
  exact ⟨hlo, hzero, hone⟩

#print axioms fission_loop_two_rounds_with_helper
end AspisR1FinishFissionHelperLoop
