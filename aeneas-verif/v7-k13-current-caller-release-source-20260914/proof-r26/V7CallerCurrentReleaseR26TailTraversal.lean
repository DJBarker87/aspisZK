import V7CallerCurrentReleaseR26TailComponentTrace

/-!
# Pointwise traversal of the accepted fused tail loop

The exact accepted loop trace maps every component through `foldTailComponent`
and writes it back at the same index.  These lemmas expose any chosen cell
without replaying the recursive generated loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailTraversal

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26TailComponentTrace

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev Component := sumcheck.WeightComponent
abbrev Components := alloc.vec.Vec Component
abbrev Weights := sumcheck.WeightAccumulator
abbrev State := Weights × Std.Usize
abbrev Output := Std.U32 × Components × Bool

deriving instance Inhabited for sumcheck.WeightComponent

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

private theorem transitionExact
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize)
    (active : index.val < weights.components.length)
    (transition : ActiveTailTransition alphas alpha2 preparedAlpha
      preparedAlpha2 alpha3 weights index) :
    transition.component = weights.components.val[index.val]! ∧
      transition.weightsOut.log_len = weights.log_len ∧
      transition.weightsOut.components =
        alloc.vec.Vec.set weights.components index transition.folded := by
  obtain ⟨value, back, read, valueExact, backExact⟩ :=
    generatedVecIndexMutSuccess weights.components index active
  rw [transition.read] at read
  have pairExact : (transition.component, transition.rebuild) =
      (value, back) := Result.ok.inj read
  have componentExact : transition.component = value :=
    congrArg (fun pair => pair.1) pairExact
  have rebuildExact : transition.rebuild = back :=
    congrArg (fun pair => pair.2) pairExact
  have rebuildSet : transition.rebuild =
      alloc.vec.Vec.set weights.components index :=
    rebuildExact.trans backExact
  refine ⟨componentExact.trans valueExact, ?_, ?_⟩
  · rw [transition.weightsOutExact]
  · rw [transition.weightsOutExact, transition.componentsOutExact,
      rebuildSet]

private theorem tracePreservesEarlierCell
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize)
    (finalLog : Std.U32) (output : Components)
    (target : Nat) (targetBefore : target < index.val)
    (targetBound : target < weights.components.val.length)
    (trace : ExactLoopTrace
      (fun state : State =>
        sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          alphas alpha2 preparedAlpha preparedAlpha2 alpha3 state.1 state.2)
      (weights, index) (finalLog, output, true)) :
    output.val[target]! = weights.components.val[target]! := by
  cases trace with
  | done edge =>
      by_cases active : index < alloc.vec.Vec.len weights.components
      · have rejected := active_tail_done_reports_false alphas alpha2
          preparedAlpha preparedAlpha2 alpha3 weights index
          (finalLog, output, true) active edge
        simp at rejected
      · unfold
          sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          at edge
        rw [if_neg active] at edge
        have outputExact : output = weights.components := by
          have tripleExact :
              (2#u32, weights.components, true) =
                (finalLog, output, true) :=
            ControlFlow.done.inj (Result.ok.inj edge)
          exact (congrArg (fun value : Output => value.2.1) tripleExact).symm
        rw [outputExact]
  | @cont _ next _ edge tail =>
      have activeNat : index.val < weights.components.length := by
        by_contra inactiveNat
        have inactive : ¬ index < alloc.vec.Vec.len weights.components := by
          scalar_tac
        unfold
          sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          at edge
        rw [if_neg inactive] at edge
        cases Result.ok.inj edge
      have active : index < alloc.vec.Vec.len weights.components := by
        scalar_tac
      obtain ⟨transition, nextExact⟩ := active_tail_edge_exposes_transition
        alphas alpha2 preparedAlpha preparedAlpha2 alpha3 weights index next
        active edge
      obtain ⟨_componentExact, logExact, componentsOutExact⟩ :=
        transitionExact alphas alpha2 preparedAlpha preparedAlpha2 alpha3
          weights index activeNat transition
      subst next
      have nextValue :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        wrappingSuccValue weights.components index activeNat
      have targetAtNext :
          transition.weightsOut.components.val[target]! =
            weights.components.val[target]! := by
        rw [componentsOutExact]
        exact List.set_getElem!_ne _ _ _ _ (by omega)
      have targetBoundNext :
          target < transition.weightsOut.components.val.length := by
        simpa [componentsOutExact, alloc.vec.Vec.set_val_eq] using targetBound
      have recurse := tracePreservesEarlierCell alphas alpha2 preparedAlpha
        preparedAlpha2 alpha3 transition.weightsOut
        (Std.Usize.wrapping_add index 1#usize) finalLog output target
        (by rw [nextValue]; omega) targetBoundNext tail
      exact recurse.trans targetAtNext
termination_by weights.components.length - index.val
decreasing_by
  simp only [componentsOutExact, alloc.vec.Vec.set_length]
  omega

theorem exact_tail_trace_preserves_length
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize)
    (finalLog : Std.U32) (output : Components)
    (trace : ExactLoopTrace
      (fun state : State =>
        sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          alphas alpha2 preparedAlpha preparedAlpha2 alpha3 state.1 state.2)
      (weights, index) (finalLog, output, true)) :
    output.val.length = weights.components.val.length := by
  cases trace with
  | done edge =>
      by_cases active : index < alloc.vec.Vec.len weights.components
      · have rejected := active_tail_done_reports_false alphas alpha2
          preparedAlpha preparedAlpha2 alpha3 weights index
          (finalLog, output, true) active edge
        simp at rejected
      · unfold
          sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          at edge
        rw [if_neg active] at edge
        have outputExact : output = weights.components := by
          have tripleExact :
              (2#u32, weights.components, true) =
                (finalLog, output, true) :=
            ControlFlow.done.inj (Result.ok.inj edge)
          exact (congrArg (fun value : Output => value.2.1) tripleExact).symm
        rw [outputExact]
  | @cont _ next _ edge tail =>
      have activeNat : index.val < weights.components.length := by
        by_contra inactiveNat
        have inactive : ¬ index < alloc.vec.Vec.len weights.components := by
          scalar_tac
        unfold
          sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          at edge
        rw [if_neg inactive] at edge
        cases Result.ok.inj edge
      have active : index < alloc.vec.Vec.len weights.components := by
        scalar_tac
      obtain ⟨transition, nextExact⟩ := active_tail_edge_exposes_transition
        alphas alpha2 preparedAlpha preparedAlpha2 alpha3 weights index next
        active edge
      obtain ⟨_componentExact, logExact, componentsOutExact⟩ :=
        transitionExact alphas alpha2 preparedAlpha preparedAlpha2 alpha3
          weights index activeNat transition
      subst next
      have nextValue :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        wrappingSuccValue weights.components index activeNat
      have recurse := exact_tail_trace_preserves_length alphas alpha2
        preparedAlpha preparedAlpha2 alpha3 transition.weightsOut
        (Std.Usize.wrapping_add index 1#usize) finalLog output tail
      calc
        output.val.length = transition.weightsOut.components.val.length :=
          recurse
        _ = weights.components.val.length := by
          simp [componentsOutExact, alloc.vec.Vec.set_val_eq]
termination_by weights.components.length - index.val
decreasing_by
  simp only [componentsOutExact, alloc.vec.Vec.set_length]
  rw [nextValue]
  omega

theorem exact_tail_trace_final_log_two
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize)
    (finalLog : Std.U32) (output : Components)
    (trace : ExactLoopTrace
      (fun state : State =>
        sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          alphas alpha2 preparedAlpha preparedAlpha2 alpha3 state.1 state.2)
      (weights, index) (finalLog, output, true)) :
    finalLog = 2#u32 := by
  cases trace with
  | done edge =>
      by_cases active : index < alloc.vec.Vec.len weights.components
      · have rejected := active_tail_done_reports_false alphas alpha2
          preparedAlpha preparedAlpha2 alpha3 weights index
          (finalLog, output, true) active edge
        simp at rejected
      · unfold
          sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          at edge
        rw [if_neg active] at edge
        have tripleExact :
            (2#u32, weights.components, true) =
              (finalLog, output, true) :=
          ControlFlow.done.inj (Result.ok.inj edge)
        exact (congrArg (fun value : Output => value.1) tripleExact).symm
  | @cont _ next _ edge tail =>
      have activeNat : index.val < weights.components.length := by
        by_contra inactiveNat
        have inactive : ¬ index < alloc.vec.Vec.len weights.components := by
          scalar_tac
        unfold
          sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          at edge
        rw [if_neg inactive] at edge
        cases Result.ok.inj edge
      have active : index < alloc.vec.Vec.len weights.components := by
        scalar_tac
      obtain ⟨transition, nextExact⟩ := active_tail_edge_exposes_transition
        alphas alpha2 preparedAlpha preparedAlpha2 alpha3 weights index next
        active edge
      obtain ⟨_componentExact, logExact, componentsOutExact⟩ :=
        transitionExact alphas alpha2 preparedAlpha preparedAlpha2 alpha3
          weights index activeNat transition
      subst next
      have nextValue :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        wrappingSuccValue weights.components index activeNat
      exact exact_tail_trace_final_log_two alphas alpha2 preparedAlpha
        preparedAlpha2 alpha3 transition.weightsOut
        (Std.Usize.wrapping_add index 1#usize) finalLog output tail
termination_by weights.components.length - index.val
decreasing_by
  simp only [componentsOutExact, alloc.vec.Vec.set_length]
  rw [nextValue]
  omega

/-- Every in-bounds cell in an accepted fused trace is the successful exact
component-step result for the corresponding input cell. -/
theorem exact_tail_trace_exposes_component
    (alphas : Array RawQM31 3#usize)
    (alpha2 : Array RawQM31 2#usize)
    (preparedAlpha : Array RawPrepared 2#usize)
    (preparedAlpha2 : Array RawPrepared 2#usize)
    (alpha3 : Array RawQM31 2#usize)
    (weights : Weights) (index : Std.Usize)
    (finalLog : Std.U32) (output : Components)
    (target : Nat) (cursorBefore : index.val ≤ target)
    (targetBound : target < weights.components.val.length)
    (trace : ExactLoopTrace
      (fun state : State =>
        sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          alphas alpha2 preparedAlpha preparedAlpha2 alpha3 state.1 state.2)
      (weights, index) (finalLog, output, true)) :
    ∃ componentOut,
      foldTailComponent alphas alpha2 preparedAlpha preparedAlpha2 alpha3
          weights.components.val[target]! = ok (some componentOut) ∧
      output.val[target]! = componentOut := by
  cases trace with
  | done edge =>
      have active : index < alloc.vec.Vec.len weights.components := by
        scalar_tac
      have rejected := active_tail_done_reports_false alphas alpha2
        preparedAlpha preparedAlpha2 alpha3 weights index
        (finalLog, output, true) active edge
      simp at rejected
  | @cont _ next _ edge tail =>
      have activeNat : index.val < weights.components.length := by
        change index.val < weights.components.val.length
        omega
      have active : index < alloc.vec.Vec.len weights.components := by
        scalar_tac
      obtain ⟨transition, nextExact⟩ := active_tail_edge_exposes_transition
        alphas alpha2 preparedAlpha preparedAlpha2 alpha3 weights index next
        active edge
      obtain ⟨componentExact, logExact, componentsOutExact⟩ :=
        transitionExact alphas alpha2 preparedAlpha preparedAlpha2 alpha3
          weights index activeNat transition
      subst next
      have nextValue :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        wrappingSuccValue weights.components index activeNat
      by_cases atTarget : index.val = target
      · have foldRun : foldTailComponent alphas alpha2 preparedAlpha
            preparedAlpha2 alpha3 weights.components.val[target]! =
            ok (some transition.folded) := by
          rw [← atTarget, ← componentExact]
          exact transition.foldRun
        have targetAtNext :
            transition.weightsOut.components.val[target]! =
              transition.folded := by
          rw [componentsOutExact]
          exact List.set_getElem!_eq _ _ _ _ ⟨targetBound, atTarget⟩
        have targetBoundNext :
            target < transition.weightsOut.components.val.length := by
          simpa [componentsOutExact, alloc.vec.Vec.set_val_eq] using targetBound
        have preserved := tracePreservesEarlierCell alphas alpha2
          preparedAlpha preparedAlpha2 alpha3 transition.weightsOut
          (Std.Usize.wrapping_add index 1#usize) finalLog output target
          (by rw [nextValue]; omega) targetBoundNext tail
        exact ⟨transition.folded, foldRun, preserved.trans targetAtNext⟩
      · have targetAtNext :
            transition.weightsOut.components.val[target]! =
              weights.components.val[target]! := by
          rw [componentsOutExact]
          exact List.set_getElem!_ne _ _ _ _ (by omega)
        have targetBoundNext :
            target < transition.weightsOut.components.val.length := by
          simpa [componentsOutExact, alloc.vec.Vec.set_val_eq] using targetBound
        obtain ⟨componentOut, foldRun, finalCell⟩ :=
          exact_tail_trace_exposes_component alphas alpha2 preparedAlpha
            preparedAlpha2 alpha3 transition.weightsOut
            (Std.Usize.wrapping_add index 1#usize) finalLog output target
            (by rw [nextValue]; omega) targetBoundNext tail
        refine ⟨componentOut, ?_, finalCell⟩
        simpa [targetAtNext] using foldRun
termination_by weights.components.length - index.val
decreasing_by
  simp only [componentsOutExact, alloc.vec.Vec.set_length]
  omega

#print axioms exact_tail_trace_exposes_component
#print axioms exact_tail_trace_preserves_length
#print axioms exact_tail_trace_final_log_two

end V7CallerCurrentReleaseR26TailTraversal
