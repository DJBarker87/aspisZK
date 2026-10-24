import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3PointScanBodyCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9LoopInvariantPropertyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9CirclePointscanControlV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3PointScanBodyCanonicalV1

theorem body_done_execution
    (z : Array Point 2#usize) (iter : R) (factors out : Factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z iter factors =
      .ok (.done out)) : out = factors ∧ ∃ iterNext,
        core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iterNext) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.done out : ControlFlow (R × Factors) Factors) at hbody
    exact ⟨(ControlFlow.done.inj (Result.ok.inj hbody)).symm, iter1, hnext⟩
  | some k =>
    obtain ⟨point, hpoint, hbody⟩ := bind_success_inv (Array.index_usize z k) _ _ hbody
    obtain ⟨q, hq, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul point.x point.y) _ _ hbody
    obtain ⟨i, hi, hbody⟩ := bind_success_inv
      (lift (Std.Usize.wrapping_add 3#usize k)) _ _ hbody
    obtain ⟨mutPair, hmut, hbody⟩ := bind_success_inv (Array.index_mut_usize factors i) _ _ hbody
    rcases mutPair with ⟨old, back⟩
    change (do
      let rowOut ← Array.update old 0#usize
        (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,
          point.y, point.x, q] : Cell)
      let x ← AspisR1S9ActualWeightsNewBoxNewV3.double point.x
      let factorsInner ← AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0
        { start := 1#usize, «end» := 5#usize } (back rowOut) k x
      ok (ControlFlow.cont (iter1, factorsInner) : ControlFlow (R × Factors) Factors)) =
        ok (ControlFlow.done out : ControlFlow (R × Factors) Factors) at hbody
    obtain ⟨rowOut, hrow, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨x, hx, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨factorsInner, hinner, hbody⟩ := bind_success_inv _ _ _ hbody
    cases hbody


#print axioms body_done_execution
end AspisR1S9CirclePointscanControlV1
