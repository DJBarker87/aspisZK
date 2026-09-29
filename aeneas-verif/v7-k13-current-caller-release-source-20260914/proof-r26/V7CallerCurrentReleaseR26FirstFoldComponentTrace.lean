import V7CallerCurrentReleaseR26WeightFoldLoopTrace

/-!
# Component-level trace for the first current weight fold

This factors the generated loop body's inline component match into an exact
definition and inverts every continuation edge into its vector read, helper
call, and write-back.  Later semantic proofs can dispatch on the retained
component without unfolding the recursive loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldComponentTrace

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev Component := sumcheck.WeightComponent
abbrev Components := alloc.vec.Vec Component
abbrev State := Components × Std.Usize

/-- The component match appearing literally inside the generated first-fold
loop body. -/
def foldDeferredComponent
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31) :
    Component → Result Component
  | .Geometric _ _ => fail panic
  | .Multilinear scale point => do
      let (scaleOut, pointOut) ←
        sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
          scale point alpha alpha2 alpha3
      ok (.Multilinear scaleOut pointOut)
  | .Tensor scale factors => do
      let (scaleOut, factorsOut) ←
        sumcheck.WeightAccumulator.impl.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2
      ok (.Tensor scaleOut factorsOut)
  | .LineM31Tensor scale x => do
      let (scaleOut, xOut) ←
        sumcheck.WeightAccumulator.impl.fold_line_m31_tensor_arity4
          scale x alpha alpha2 alpha3
      ok (.LineM31Tensor scaleOut xOut)
  | .LineM31Batch scales xs deferred => do
      let (scaleSlice, rebuildScales) ← lift (alloc.vec.Vec.deref_mut scales)
      let (xSlice, rebuildXs) ← lift (alloc.vec.Vec.deref_mut xs)
      let (scalesOut, xsOut, deferredOut) ←
        sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
          scaleSlice xSlice deferred alpha alpha2 alpha3
      ok (.LineM31Batch (rebuildScales scalesOut) (rebuildXs xsOut)
        deferredOut)
  | .Product _ _ => fail panic
  | .Dense values => do
      let valuesOut ←
        sumcheck.WeightAccumulator.impl.fold_dense_arity4
          values alpha alpha2 alpha3
      ok (.Dense valuesOut)
  | .Grouped64x16 _ _ _ => fail panic
  | .Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues =>
      do
      let (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut) ←
        sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
          rowGroups groupMasks firstAlpha groupValues currentLogLen
          alpha alpha2 alpha3
      ok (.Grouped64x16BinaryDeferred rowGroupsOut groupMasksOut
        firstAlphaOut groupValuesOut)
  | .Grouped128x16 _ _ _ => fail panic

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

structure ActiveDeferredTransition
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (components : Components) (index : Std.Usize) : Type where
  component : Component
  rebuild : Component → Components
  folded : Component
  componentsOut : Components
  read : alloc.vec.Vec.index_mut
    (core.slice.index.SliceIndexUsizeSlice Component) components index =
      ok (component, rebuild)
  foldRun : foldDeferredComponent currentLogLen alpha alpha2 preparedAlpha
    preparedAlpha2 alpha3 component = ok folded
  componentsOutExact : componentsOut = rebuild folded

/-- Every continuation edge is one successful source component fold followed
by the exact mutable-vector write-back. -/
theorem active_deferred_edge_exposes_transition
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (components : Components) (index : Std.Usize) (next : State)
    (active : index < alloc.vec.Vec.len components)
    (edge :
      sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
        currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
        components index = ok (cont next)) :
    ∃ transition : ActiveDeferredTransition currentLogLen alpha alpha2
        preparedAlpha preparedAlpha2 alpha3 components index,
      next = (transition.componentsOut,
        Std.Usize.wrapping_add index 1#usize) := by
  unfold
    sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
    at edge
  rw [if_pos active] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨pair, read, edge⟩ := edge
  rcases pair with ⟨component, rebuild⟩
  have factoredEdge : (do
      let folded ← foldDeferredComponent currentLogLen alpha alpha2
        preparedAlpha preparedAlpha2 alpha3 component
      let componentsOut := rebuild folded
      let indexOut ← lift (Std.Usize.wrapping_add index 1#usize)
      ok (cont (componentsOut, indexOut) : ControlFlow State Components)) =
        ok (cont next : ControlFlow State Components) := by
    cases component <;>
      simpa only [foldDeferredComponent, result_bind_assoc] using edge
  rw [bind_eq_ok_iff] at factoredEdge
  obtain ⟨folded, foldRun, factoredEdge⟩ := factoredEdge
  simp only [Std.lift, Bind.bind, Aeneas.Std.bind] at factoredEdge
  have nextExact : next =
      (rebuild folded, Std.Usize.wrapping_add index 1#usize) :=
    ControlFlow.cont.inj (Result.ok.inj factoredEdge).symm
  let transition : ActiveDeferredTransition currentLogLen alpha alpha2
      preparedAlpha preparedAlpha2 alpha3 components index := {
    component := component
    rebuild := rebuild
    folded := folded
    componentsOut := rebuild folded
    read := read
    foldRun := foldRun
    componentsOutExact := rfl }
  exact ⟨transition, nextExact⟩

#print axioms active_deferred_edge_exposes_transition

end V7CallerCurrentReleaseR26FirstFoldComponentTrace
