import V7CallerCurrentReleaseR26TailTraversal

/-!
# Exact six-component output of the accepted fused tail

The post-merge accumulator has six components.  This module applies the
pointwise traversal theorem at all six indices and packages the exact source
step and returned component for each one.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailSixSource

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR26TailComponentTrace
open V7CallerCurrentReleaseR26TailTraversal

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev Component := sumcheck.WeightComponent

structure TailSixSourceTrace
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (component0 component1 component2 component3 component4 component5 :
      Component) : Type where
  loopTrace : ExactLoopTrace
    (fun state : sumcheck.WeightAccumulator × Std.Usize =>
      sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
        alphas
        (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
        (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
        (Array.make 2#usize
          [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
        (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
        state.1 state.2)
    (tail.afterMerge, 0#usize)
    (tail.finalLogLen, tail.finalComponents, true)
  out0 : Component
  out1 : Component
  out2 : Component
  out3 : Component
  out4 : Component
  out5 : Component
  fold0 : foldTailComponent alphas
    (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed]) component0 =
      ok (some out0)
  fold1 : foldTailComponent alphas
    (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed]) component1 =
      ok (some out1)
  fold2 : foldTailComponent alphas
    (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed]) component2 =
      ok (some out2)
  fold3 : foldTailComponent alphas
    (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed]) component3 =
      ok (some out3)
  fold4 : foldTailComponent alphas
    (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed]) component4 =
      ok (some out4)
  fold5 : foldTailComponent alphas
    (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed]) component5 =
      ok (some out5)
  finalLogExact : tail.finalLogLen = 2#u32
  finalComponentsExact : tail.finalComponents.val =
    [out0, out1, out2, out3, out4, out5]

theorem accepted_tail_exposes_six_source_components
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (component0 component1 component2 component3 component4 component5 :
      Component)
    (componentsExact : tail.afterMerge.components.val =
      [component0, component1, component2, component3, component4,
        component5]) :
    Nonempty (TailSixSourceTrace tail component0 component1 component2
      component3 component4 component5) := by
  let loopTrace := Classical.choice
    (accepted_tail_traversal_exposes_exact_trace tail)
  have inputLength : tail.afterMerge.components.val.length = 6 := by
    simp [componentsExact]
  obtain ⟨out0, fold0Raw, cell0⟩ := exact_tail_trace_exposes_component
    alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
    tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents 0
    (by norm_num) (by omega) loopTrace
  obtain ⟨out1, fold1Raw, cell1⟩ := exact_tail_trace_exposes_component
    alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
    tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents 1
    (by norm_num) (by omega) loopTrace
  obtain ⟨out2, fold2Raw, cell2⟩ := exact_tail_trace_exposes_component
    alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
    tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents 2
    (by norm_num) (by omega) loopTrace
  obtain ⟨out3, fold3Raw, cell3⟩ := exact_tail_trace_exposes_component
    alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
    tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents 3
    (by norm_num) (by omega) loopTrace
  obtain ⟨out4, fold4Raw, cell4⟩ := exact_tail_trace_exposes_component
    alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
    tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents 4
    (by norm_num) (by omega) loopTrace
  obtain ⟨out5, fold5Raw, cell5⟩ := exact_tail_trace_exposes_component
    alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
    tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents 5
    (by norm_num) (by omega) loopTrace
  have fold0 := fold0Raw
  have fold1 := fold1Raw
  have fold2 := fold2Raw
  have fold3 := fold3Raw
  have fold4 := fold4Raw
  have fold5 := fold5Raw
  simp only [componentsExact, List.getElem!_cons_zero,
    List.getElem!_cons_succ] at fold0 fold1 fold2 fold3 fold4 fold5
  have finalLogExact := exact_tail_trace_final_log_two
    alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
    (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
    (Array.make 2#usize
      [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
    (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
    tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents loopTrace
  have outputLength : tail.finalComponents.val.length = 6 := by
    have preserved := exact_tail_trace_preserves_length
      alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      tail.afterMerge 0#usize tail.finalLogLen tail.finalComponents loopTrace
    omega
  have finalComponentsExact : tail.finalComponents.val =
      [out0, out1, out2, out3, out4, out5] := by
    apply List.ext_getElem
    · simpa using outputLength
    · intro index leftBound rightBound
      rw [List.Inhabited_getElem_eq_getElem!
        tail.finalComponents.val index leftBound]
      have indexBound : index < 6 := by simpa using rightBound
      interval_cases index
      · simpa only [List.getElem_cons_zero] using cell0
      · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
          cell1
      · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
          cell2
      · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
          cell3
      · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
          cell4
      · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
          cell5
  exact ⟨{
    loopTrace := loopTrace
    out0 := out0
    out1 := out1
    out2 := out2
    out3 := out3
    out4 := out4
    out5 := out5
    fold0 := fold0
    fold1 := fold1
    fold2 := fold2
    fold3 := fold3
    fold4 := fold4
    fold5 := fold5
    finalLogExact := finalLogExact
    finalComponentsExact := finalComponentsExact }⟩

#print axioms accepted_tail_exposes_six_source_components

end V7CallerCurrentReleaseR26TailSixSource
