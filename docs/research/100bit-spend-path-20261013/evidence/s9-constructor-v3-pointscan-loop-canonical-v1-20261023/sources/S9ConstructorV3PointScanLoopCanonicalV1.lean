import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3PointScanBodyCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9LoopInvariantPropertyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3PointScanLoopCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3PointScanBodyCanonicalV1

private theorem body_done_same_factors
    (z : Array Point 2#usize) (iter : R) (factors out : Factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z iter factors =
      .ok (.done out)) : out = factors := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.done out : ControlFlow (R × Factors) Factors) at hbody
    exact (ControlFlow.done.inj (Result.ok.inj hbody)).symm
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

private def scanBody (z : Array Point 2#usize) (state : R × Factors) :
    Result (ControlFlow (R × Factors) Factors) :=
  AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z state.1 state.2

private def scanInvariant (state : R × Factors) : Prop := FactorsCanonical state.2
private def scanMeasure (state : R × Factors) : Nat := state.1.end.val - state.1.start.val

/-- The complete generated pointscan loop preserves canonical factor arrays.
All successful child calls are obtained from the same loop execution, and the
point coordinate condition is a read contract on the exact input array. -/
theorem pointscan_loop_success_canonical
    (z : Array Point 2#usize) (iter : R) (factors out : Factors)
    (hz : PointsCanonical z) (hfactors : FactorsCanonical factors)
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1 iter z factors = .ok out) :
    FactorsCanonical out := by
  let step : (R × Factors) → Result (ControlFlow (R × Factors) Factors) := scanBody z
  have hdone : ∀ s out, scanInvariant s → step s = .ok (.done out) → FactorsCanonical out := by
    rintro ⟨iter, factors⟩ out hs hstep
    have hsame := body_done_same_factors z iter factors out hstep
    subst out
    exact hs
  have hcontinue : ∀ s s', scanInvariant s → step s = .ok (.cont s') → scanInvariant s' := by
    rintro ⟨iter, factors⟩ ⟨iterNext, factorsNext⟩ hs hstep
    exact pointscan_body_success_canonical z iter iterNext factors factorsNext hz hs hstep
  have hdecrease : ∀ s s', step s = .ok (.cont s') → scanMeasure s' < scanMeasure s := by
    rintro ⟨iter, factors⟩ ⟨iterNext, factorsNext⟩ hstep
    obtain ⟨k, point, q, i, old, back, rowOut, x, hnext, hrest⟩ :=
      pointscan_body_success_has_execution z iter iterNext factors factorsNext hstep
    obtain ⟨hlt, hd, hstart, hend⟩ := next_some_progress iter iterNext k hnext
    simp only [scanMeasure, hstart, hend]
    omega
  have hloop' : Aeneas.Std.loop step (iter, factors) = .ok out := by
    change Aeneas.Std.loop (scanBody z) (iter, factors) = .ok out at hloop
    exact hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step scanMeasure scanInvariant FactorsCanonical hdone hcontinue hdecrease
    (iter, factors) out hfactors hloop'

#print axioms pointscan_loop_success_canonical
end AspisR1S9ConstructorV3PointScanLoopCanonicalV1
