import V7CallerCurrentReleaseR26WeightFoldLoopTrace

/-!
# Component step of the accepted fused tail traversal

This factors the generated component match into an exact option-valued step.
`none` represents every source branch which terminates the traversal with
`false`; `some component` represents the successful write-back and cursor
advance.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailComponentTrace

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev Component := sumcheck.WeightComponent
abbrev Components := alloc.vec.Vec Component
abbrev Weights := sumcheck.WeightAccumulator
abbrev State := Weights × Std.Usize
abbrev Output := Std.U32 × Components × Bool

def foldTailComponent
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize) :
    Component → Result (Option Component)
  | .Geometric _ _ => ok none
  | .Multilinear scale point => do
      let alphaOne ← alphas.index_usize 1#usize
      let alphaOneSquared ← alpha2.index_usize 0#usize
      let alphaOneCubed ← alpha3.index_usize 0#usize
      let (scaleOne, pointOne) ←
        sumcheck.WeightAccumulator.impl.fold_multilinear_arity4 scale point
          alphaOne alphaOneSquared alphaOneCubed
      let alphaTwo ← alphas.index_usize 2#usize
      let alphaTwoSquared ← alpha2.index_usize 1#usize
      let alphaTwoCubed ← alpha3.index_usize 1#usize
      let (scaleTwo, pointTwo) ←
        sumcheck.WeightAccumulator.impl.fold_multilinear_arity4 scaleOne
          pointOne alphaTwo alphaTwoSquared alphaTwoCubed
      ok (some (.Multilinear scaleTwo pointTwo))
  | .Tensor scale factors => do
      let alphaOneCubed ← alpha3.index_usize 0#usize
      let preparedOne ← preparedAlpha.index_usize 0#usize
      let preparedOneSquared ← preparedAlpha2.index_usize 0#usize
      let (scaleOne, factorsOne) ←
        sumcheck.WeightAccumulator.impl.fold_tensor_arity4 scale factors
          alphaOneCubed preparedOne preparedOneSquared
      let alphaTwoCubed ← alpha3.index_usize 1#usize
      let preparedTwo ← preparedAlpha.index_usize 1#usize
      let preparedTwoSquared ← preparedAlpha2.index_usize 1#usize
      let (scaleTwo, factorsTwo) ←
        sumcheck.WeightAccumulator.impl.fold_tensor_arity4 scaleOne factorsOne
          alphaTwoCubed preparedTwo preparedTwoSquared
      ok (some (.Tensor scaleTwo factorsTwo))
  | .LineM31Tensor scale x => do
      let alphaOne ← alphas.index_usize 1#usize
      let alphaOneSquared ← alpha2.index_usize 0#usize
      let alphaOneCubed ← alpha3.index_usize 0#usize
      let (scaleOne, xOne) ←
        sumcheck.WeightAccumulator.impl.fold_line_m31_tensor_arity4 scale x
          alphaOne alphaOneSquared alphaOneCubed
      let alphaTwo ← alphas.index_usize 2#usize
      let alphaTwoSquared ← alpha2.index_usize 1#usize
      let alphaTwoCubed ← alpha3.index_usize 1#usize
      let (scaleTwo, xTwo) ←
        sumcheck.WeightAccumulator.impl.fold_line_m31_tensor_arity4 scaleOne
          xOne alphaTwo alphaTwoSquared alphaTwoCubed
      ok (some (.LineM31Tensor scaleTwo xTwo))
  | .LineM31Batch scales xs deferred => do
      let (scaleSlice, rebuildScales) ← lift (alloc.vec.Vec.deref_mut scales)
      let (xSlice, rebuildXs) ← lift (alloc.vec.Vec.deref_mut xs)
      let alphaOne ← alphas.index_usize 1#usize
      let alphaOneSquared ← alpha2.index_usize 0#usize
      let alphaOneCubed ← alpha3.index_usize 0#usize
      let (scalesOne, xsOne, deferredOne) ←
        sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4 scaleSlice
          xSlice deferred alphaOne alphaOneSquared alphaOneCubed
      let xsOneVec := rebuildXs xsOne
      let scalesOneVec := rebuildScales scalesOne
      let (scaleSliceOne, rebuildScalesOne) ←
        lift (alloc.vec.Vec.deref_mut scalesOneVec)
      let (xSliceOne, rebuildXsOne) ←
        lift (alloc.vec.Vec.deref_mut xsOneVec)
      let alphaTwo ← alphas.index_usize 2#usize
      let alphaTwoSquared ← alpha2.index_usize 1#usize
      let alphaTwoCubed ← alpha3.index_usize 1#usize
      let (scalesTwo, xsTwo, deferredTwo) ←
        sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
          scaleSliceOne xSliceOne deferredOne alphaTwo alphaTwoSquared
          alphaTwoCubed
      ok (some (.LineM31Batch (rebuildScalesOne scalesTwo)
        (rebuildXsOne xsTwo) deferredTwo))
  | .Product _ _ => ok none
  | .Dense values => do
      let alphaOne ← alphas.index_usize 1#usize
      let alphaOneSquared ← alpha2.index_usize 0#usize
      let alphaOneCubed ← alpha3.index_usize 0#usize
      let valuesOne ← sumcheck.WeightAccumulator.impl.fold_dense_arity4
        values alphaOne alphaOneSquared alphaOneCubed
      let alphaTwo ← alphas.index_usize 2#usize
      let alphaTwoSquared ← alpha2.index_usize 1#usize
      let alphaTwoCubed ← alpha3.index_usize 1#usize
      let valuesTwo ← sumcheck.WeightAccumulator.impl.fold_dense_arity4
        valuesOne alphaTwo alphaTwoSquared alphaTwoCubed
      ok (some (.Dense valuesTwo))
  | .Grouped64x16 _ _ _ => ok none
  | .Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues =>
      do
      let masksEmpty ← alloc.vec.Vec.is_empty Global groupMasks
      if masksEmpty then
        if core.option.Option.is_some firstAlpha then
          ok none
        else if alloc.vec.Vec.len rowGroups != 64#usize then
          ok none
        else
          let alphaOne ← alphas.index_usize 1#usize
          let alphaTwo ← alphas.index_usize 2#usize
          let (foldedGroups, foldedValues) ←
            sumcheck.fold_grouped_rows_twice (alloc.vec.Vec.deref rowGroups)
              (alloc.vec.Vec.deref groupValues) alphaOne alphaTwo
          ok (some (.Grouped64x16BinaryDeferred foldedGroups groupMasks
            firstAlpha foldedValues))
      else ok none
  | .Grouped128x16 _ _ _ => ok none

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem result_bind_assoc {A B C : Type}
    (input : Result A) (middle : A → Result B) (next : B → Result C) :
    (do
      let y ← (do
        let x ← input
        middle x)
      next y) =
      (do
        let x ← input
        let y ← middle x
        next y) := by
  cases input <;> rfl

structure ActiveTailTransition
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize) : Type where
  component : Component
  rebuild : Component → Components
  folded : Component
  componentsOut : Components
  weightsOut : Weights
  read : alloc.vec.Vec.index_mut
    (core.slice.index.SliceIndexUsizeSlice Component) weights.components index =
      ok (component, rebuild)
  foldRun : foldTailComponent alphas alpha2 preparedAlpha preparedAlpha2
    alpha3 component = ok (some folded)
  componentsOutExact : componentsOut = rebuild folded
  weightsOutExact : weightsOut = { weights with components := componentsOut }

/-- Every continuation edge of the fused traversal is exactly one successful
option-valued component step followed by its in-place vector write-back. -/
theorem active_tail_edge_exposes_transition
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize) (next : State)
    (active : index < alloc.vec.Vec.len weights.components)
    (edge :
      sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
        alphas alpha2 preparedAlpha preparedAlpha2 alpha3 weights index =
          ok (cont next)) :
    ∃ transition : ActiveTailTransition alphas alpha2 preparedAlpha
        preparedAlpha2 alpha3 weights index,
      next = (transition.weightsOut,
        Std.Usize.wrapping_add index 1#usize) := by
  unfold
    sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
    at edge
  rw [if_pos active] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨pair, read, edge⟩ := edge
  rcases pair with ⟨component, rebuild⟩
  have factoredEdge : (do
      let folded? ← foldTailComponent alphas alpha2 preparedAlpha
        preparedAlpha2 alpha3 component
      match folded? with
      | none => ok (done (weights.log_len, rebuild component, false))
      | some folded =>
          let componentsOut := rebuild folded
          let indexOut ← lift (Std.Usize.wrapping_add index 1#usize)
          ok (cont ({ weights with components := componentsOut }, indexOut))) =
        ok (cont next : ControlFlow State Output) := by
    cases component <;>
      simp only [foldTailComponent, result_bind_assoc, bind_tc_ok] at edge ⊢
    all_goals try exact edge
    case Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues =>
      cases emptyEquation : alloc.vec.Vec.is_empty Global groupMasks with
      | fail error => simp [emptyEquation] at edge
      | div => simp [emptyEquation] at edge
      | ok empty =>
          cases empty with
          | false => simpa [emptyEquation] using edge
          | true =>
              cases firstAlpha with
              | some first => simp [emptyEquation] at edge
              | none =>
                  by_cases wrongLength :
                      alloc.vec.Vec.len rowGroups != 64#usize
                  · simp [emptyEquation, wrongLength] at edge
                  · simpa [emptyEquation, wrongLength, result_bind_assoc,
                      bind_tc_ok] using edge
  rw [bind_eq_ok_iff] at factoredEdge
  obtain ⟨folded?, foldRun, factoredEdge⟩ := factoredEdge
  cases folded? with
  | none => simp at factoredEdge
  | some folded =>
      simp only [Std.lift, Bind.bind, Aeneas.Std.bind] at factoredEdge
      have nextExact : next =
          ({ weights with components := rebuild folded },
            Std.Usize.wrapping_add index 1#usize) :=
        ControlFlow.cont.inj (Result.ok.inj factoredEdge).symm
      let transition : ActiveTailTransition alphas alpha2 preparedAlpha
          preparedAlpha2 alpha3 weights index := {
        component := component
        rebuild := rebuild
        folded := folded
        componentsOut := rebuild folded
        weightsOut := { weights with components := rebuild folded }
        read := read
        foldRun := foldRun
        componentsOutExact := rfl
        weightsOutExact := rfl }
      exact ⟨transition, nextExact⟩

/-- Every active early terminal edge is one of the generated rejection
branches and therefore reports `false`. -/
theorem active_tail_done_reports_false
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize) (output : Output)
    (active : index < alloc.vec.Vec.len weights.components)
    (edge :
      sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
        alphas alpha2 preparedAlpha preparedAlpha2 alpha3 weights index =
          ok (done output)) :
    output.2.2 = false := by
  unfold
    sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
    at edge
  rw [if_pos active] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨pair, read, edge⟩ := edge
  rcases pair with ⟨component, rebuild⟩
  have factoredEdge : (do
      let folded? ← foldTailComponent alphas alpha2 preparedAlpha
        preparedAlpha2 alpha3 component
      match folded? with
      | none => ok (done (weights.log_len, rebuild component, false))
      | some folded =>
          let componentsOut := rebuild folded
          let indexOut ← lift (Std.Usize.wrapping_add index 1#usize)
          ok (cont ({ weights with components := componentsOut }, indexOut))) =
        ok (done output : ControlFlow State Output) := by
    cases component <;>
      simp only [foldTailComponent, result_bind_assoc, bind_tc_ok] at edge ⊢
    all_goals try exact edge
    case Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues =>
      cases emptyEquation : alloc.vec.Vec.is_empty Global groupMasks with
      | fail error => simp [emptyEquation] at edge
      | div => simp [emptyEquation] at edge
      | ok empty =>
          cases empty with
          | false => simpa [emptyEquation] using edge
          | true =>
              cases firstAlpha with
              | some first => simpa [emptyEquation] using edge
              | none =>
                  by_cases wrongLength :
                      alloc.vec.Vec.len rowGroups != 64#usize
                  · simpa [emptyEquation, wrongLength] using edge
                  · simpa [emptyEquation, wrongLength, result_bind_assoc,
                      bind_tc_ok] using edge
  rw [bind_eq_ok_iff] at factoredEdge
  obtain ⟨folded?, _foldRun, factoredEdge⟩ := factoredEdge
  cases folded? with
  | none =>
      have outputExact :
          (weights.log_len, rebuild component, false) = output :=
        ControlFlow.done.inj (Result.ok.inj factoredEdge)
      exact (congrArg (fun value : Output => value.2.2) outputExact).symm
  | some folded => cases Result.ok.inj factoredEdge

#print axioms active_tail_edge_exposes_transition
#print axioms active_tail_done_reports_false

end V7CallerCurrentReleaseR26TailComponentTrace
