import V7CallerCurrentReleaseR26FirstFoldComponentTrace

/-!
# Pointwise traversal of the current first-fold component loop

The exact finite trace maps every input vector cell through
`foldDeferredComponent` and writes the result back at the same index.  These
lemmas establish that fact without replaying the recursive generated loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldTraversal

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26FirstFoldComponentTrace

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev Component := sumcheck.WeightComponent
abbrev Components := alloc.vec.Vec Component
abbrev State := Components × Std.Usize

deriving instance Inhabited for sumcheck.WeightComponent

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

private theorem generatedVecIndexMutSuccess
    (values : Components) (index : Std.Usize)
    (inBounds : index.val < values.length) :
    ∃ value back,
      alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Component) values index =
        ok (value, back) ∧
      value = values.val[index.val]! ∧
      back = alloc.vec.Vec.set values index := by
  obtain ⟨pair, run, post⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec values index inBounds)
  rcases pair with ⟨value, back⟩
  refine ⟨value, back, ?_, ?_, post.2⟩
  · rw [alloc.vec.Vec.index_mut_slice_index]
    exact run
  · rw [post.1]
    symm
    apply List.getElem!_of_getElem?
    simpa using inBounds

private theorem wrappingSuccValue
    (components : Components) (index : Std.Usize)
    (active : index.val < components.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have oneValue : (1#usize : Std.Usize).val = 1 := rfl
  rw [oneValue]
  apply Nat.mod_eq_of_lt
  have lengthWithinScalar : components.length < UScalar.size .Usize := by
    simpa using (alloc.vec.Vec.len components).hSize
  omega

private theorem activeEdgeIsContinuation
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (components : Components) (index : Std.Usize)
    (flow : ControlFlow State Components)
    (active : index < alloc.vec.Vec.len components)
    (edge :
      sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
        currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
        components index = ok flow) :
    ∃ next, flow = cont next := by
  unfold
    sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
    at edge
  rw [if_pos active] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨pair, _read, edge⟩ := edge
  rcases pair with ⟨component, rebuild⟩
  have factoredEdge : (do
      let folded ← foldDeferredComponent currentLogLen alpha alpha2
        preparedAlpha preparedAlpha2 alpha3 component
      let componentsOut := rebuild folded
      let indexOut ← lift (Std.Usize.wrapping_add index 1#usize)
      ok (cont (componentsOut, indexOut) : ControlFlow State Components)) =
        ok flow := by
    cases component <;>
      simpa only [foldDeferredComponent, result_bind_assoc] using edge
  rw [bind_eq_ok_iff] at factoredEdge
  obtain ⟨folded, _foldRun, factoredEdge⟩ := factoredEdge
  simp only [Std.lift, Bind.bind, Aeneas.Std.bind] at factoredEdge
  refine ⟨(rebuild folded, Std.Usize.wrapping_add index 1#usize), ?_⟩
  exact (Result.ok.inj factoredEdge).symm

private theorem transitionExact
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (components : Components) (index : Std.Usize)
    (active : index.val < components.length)
    (transition : ActiveDeferredTransition currentLogLen alpha alpha2
      preparedAlpha preparedAlpha2 alpha3 components index) :
    transition.component = components.val[index.val]! ∧
      transition.rebuild = alloc.vec.Vec.set components index ∧
      transition.componentsOut =
        alloc.vec.Vec.set components index transition.folded := by
  obtain ⟨value, back, read, valueExact, backExact⟩ :=
    generatedVecIndexMutSuccess components index active
  rw [transition.read] at read
  have pairExact : (transition.component, transition.rebuild) =
      (value, back) := Result.ok.inj read
  have componentExact : transition.component = value :=
    congrArg (fun pair => pair.1) pairExact
  have rebuildExact : transition.rebuild = back :=
    congrArg (fun pair => pair.2) pairExact
  have rebuildSet : transition.rebuild = alloc.vec.Vec.set components index :=
    rebuildExact.trans backExact
  refine ⟨componentExact.trans valueExact, rebuildSet, ?_⟩
  rw [transition.componentsOutExact, rebuildSet]

private theorem tracePreservesEarlierCell
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (components : Components) (index : Std.Usize) (output : Components)
    (target : Nat)
    (targetBefore : target < index.val)
    (targetBound : target < components.val.length)
    (trace : ExactLoopTrace
      (fun state : State =>
        sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
          currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
          state.1 state.2)
      (components, index) output) :
    output.val[target]! = components.val[target]! := by
  cases trace with
  | done edge =>
      have inactive : ¬ index < alloc.vec.Vec.len components := by
        intro active
        obtain ⟨next, impossible⟩ := activeEdgeIsContinuation
          currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
          components index (done output) active edge
        cases impossible
      unfold
        sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
        at edge
      rw [if_neg inactive] at edge
      have outputExact : output = components :=
        ControlFlow.done.inj (Result.ok.inj edge).symm
      rw [outputExact]
  | @cont _ next _ edge tail =>
      have activeNat : index.val < components.length := by
        by_contra inactiveNat
        have inactive : ¬ index < alloc.vec.Vec.len components := by
          scalar_tac
        unfold
          sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
          at edge
        rw [if_neg inactive] at edge
        cases Result.ok.inj edge
      have active : index < alloc.vec.Vec.len components := by scalar_tac
      obtain ⟨transition, nextExact⟩ :=
        active_deferred_edge_exposes_transition currentLogLen alpha alpha2
          preparedAlpha preparedAlpha2 alpha3 components index next active edge
      obtain ⟨_componentExact, _rebuildExact, componentsOutExact⟩ :=
        transitionExact currentLogLen alpha alpha2 preparedAlpha preparedAlpha2
          alpha3 components index activeNat transition
      subst next
      have nextValue :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        wrappingSuccValue components index activeNat
      have targetAtNext :
          transition.componentsOut.val[target]! =
            components.val[target]! := by
        rw [componentsOutExact]
        exact List.set_getElem!_ne _ _ _ _ (by omega)
      have targetBoundNext :
          target < transition.componentsOut.val.length := by
        simpa [componentsOutExact, alloc.vec.Vec.set_val_eq] using targetBound
      have recurse := tracePreservesEarlierCell currentLogLen alpha alpha2
        preparedAlpha preparedAlpha2 alpha3 transition.componentsOut
        (Std.Usize.wrapping_add index 1#usize) output target
        (by rw [nextValue]; omega) targetBoundNext tail
      exact recurse.trans targetAtNext
termination_by components.length - index.val
decreasing_by
  simp only [componentsOutExact, alloc.vec.Vec.set_length]
  omega

/-- The component traversal only overwrites cells, so its successful exact
trace preserves the vector length. -/
theorem exact_trace_preserves_length
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (components : Components) (index : Std.Usize) (output : Components)
    (trace : ExactLoopTrace
      (fun state : State =>
        sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
          currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
          state.1 state.2)
      (components, index) output) :
    output.val.length = components.val.length := by
  cases trace with
  | done edge =>
      by_cases active : index < alloc.vec.Vec.len components
      · obtain ⟨next, impossible⟩ := activeEdgeIsContinuation
          currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
          components index (done output) active edge
        cases impossible
      · unfold
          sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
          at edge
        rw [if_neg active] at edge
        have outputExact : output = components :=
          ControlFlow.done.inj (Result.ok.inj edge).symm
        rw [outputExact]
  | @cont _ next _ edge tail =>
      have activeNat : index.val < components.length := by
        by_contra inactiveNat
        have inactive : ¬ index < alloc.vec.Vec.len components := by
          scalar_tac
        unfold
          sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
          at edge
        rw [if_neg inactive] at edge
        cases Result.ok.inj edge
      have active : index < alloc.vec.Vec.len components := by scalar_tac
      obtain ⟨transition, nextExact⟩ :=
        active_deferred_edge_exposes_transition currentLogLen alpha alpha2
          preparedAlpha preparedAlpha2 alpha3 components index next active edge
      obtain ⟨_componentExact, _rebuildExact, componentsOutExact⟩ :=
        transitionExact currentLogLen alpha alpha2 preparedAlpha preparedAlpha2
          alpha3 components index activeNat transition
      subst next
      have nextValue :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        wrappingSuccValue components index activeNat
      have recurse := exact_trace_preserves_length currentLogLen alpha alpha2
        preparedAlpha preparedAlpha2 alpha3 transition.componentsOut
        (Std.Usize.wrapping_add index 1#usize) output tail
      calc
        output.val.length = transition.componentsOut.val.length := recurse
        _ = components.val.length := by
          simp [componentsOutExact, alloc.vec.Vec.set_val_eq]
termination_by components.length - index.val
decreasing_by
  simp only [componentsOutExact, alloc.vec.Vec.set_length]
  omega

/-- Every in-bounds target in an exact first-fold trace is the successful
component helper result for the input cell at that same index. -/
theorem exact_trace_exposes_component
    (currentLogLen : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (components output : Components) (index : Std.Usize) (target : Nat)
    (cursorBefore : index.val ≤ target)
    (targetBound : target < components.val.length)
    (trace : ExactLoopTrace
      (fun state : State =>
        sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
          currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
          state.1 state.2)
      (components, index) output) :
    ∃ componentOut,
      foldDeferredComponent currentLogLen alpha alpha2 preparedAlpha
          preparedAlpha2 alpha3 components.val[target]! = ok componentOut ∧
      output.val[target]! = componentOut := by
  cases trace with
  | done edge =>
      have active : index < alloc.vec.Vec.len components := by scalar_tac
      obtain ⟨next, impossible⟩ := activeEdgeIsContinuation
        currentLogLen alpha alpha2 preparedAlpha preparedAlpha2 alpha3
        components index (done output) active edge
      cases impossible
  | @cont _ next _ edge tail =>
      have activeNat : index.val < components.length := by
        change index.val < components.val.length
        omega
      have active : index < alloc.vec.Vec.len components := by scalar_tac
      obtain ⟨transition, nextExact⟩ :=
        active_deferred_edge_exposes_transition currentLogLen alpha alpha2
          preparedAlpha preparedAlpha2 alpha3 components index next active edge
      obtain ⟨componentExact, _rebuildExact, componentsOutExact⟩ :=
        transitionExact currentLogLen alpha alpha2 preparedAlpha preparedAlpha2
          alpha3 components index activeNat transition
      subst next
      have nextValue :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        wrappingSuccValue components index activeNat
      by_cases atTarget : index.val = target
      · have foldRun : foldDeferredComponent currentLogLen alpha alpha2
            preparedAlpha preparedAlpha2 alpha3 components.val[target]! =
            ok transition.folded := by
          rw [← atTarget, ← componentExact]
          exact transition.foldRun
        have targetAtNext : transition.componentsOut.val[target]! =
            transition.folded := by
          rw [componentsOutExact]
          exact List.set_getElem!_eq _ _ _ _ ⟨targetBound, atTarget⟩
        have targetBoundNext : target < transition.componentsOut.val.length := by
          simpa [componentsOutExact, alloc.vec.Vec.set_val_eq] using targetBound
        have preserved := tracePreservesEarlierCell currentLogLen alpha alpha2
          preparedAlpha preparedAlpha2 alpha3 transition.componentsOut
          (Std.Usize.wrapping_add index 1#usize) output target
          (by rw [nextValue]; omega) targetBoundNext tail
        exact ⟨transition.folded, foldRun, preserved.trans targetAtNext⟩
      · have targetAtNext : transition.componentsOut.val[target]! =
            components.val[target]! := by
          rw [componentsOutExact]
          exact List.set_getElem!_ne _ _ _ _ (by omega)
        have targetBoundNext : target < transition.componentsOut.val.length := by
          simpa [componentsOutExact, alloc.vec.Vec.set_val_eq] using targetBound
        obtain ⟨componentOut, foldRun, finalCell⟩ :=
          exact_trace_exposes_component currentLogLen alpha alpha2
            preparedAlpha preparedAlpha2 alpha3 transition.componentsOut output
            (Std.Usize.wrapping_add index 1#usize) target
            (by rw [nextValue]; omega) targetBoundNext tail
        refine ⟨componentOut, ?_, finalCell⟩
        simpa [targetAtNext] using foldRun
termination_by components.length - index.val
decreasing_by
  simp only [componentsOutExact, alloc.vec.Vec.set_length]
  omega

#print axioms exact_trace_exposes_component
#print axioms exact_trace_preserves_length

end V7CallerCurrentReleaseR26FirstFoldTraversal
