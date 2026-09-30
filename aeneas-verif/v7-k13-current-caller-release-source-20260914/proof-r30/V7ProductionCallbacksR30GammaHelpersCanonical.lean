import V7ProductionCallbacksR30GammaC1Canonical

/-! Canonicality of the helper contribution to the production packed gamma fold. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30GammaHelpersCanonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30KaratsubaCanonical
open V7ProductionCallbacksR30Qm31Canonical
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace

local instance : Inhabited CallbackQM31 :=
  ⟨V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩

abbrev Iter := Enum CallbackQM31
abbrev FinalState := Iter × (Iter → Iter)
abbrev Helper := Array CallbackQM31 4#usize
abbrev HelperIter := Enum Helper
abbrev Helpers := Array Helper 3#usize
abbrev Prepared := Array CallbackPreparedQM31 3#usize

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private def finalBody (powers : Prepared) (helpers : Helpers) (state : FinalState) :
    Result (ControlFlow FinalState Iter) :=
  V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0.body
    powers helpers state.1 state.2

private theorem final_trace_canonical
    (powers : Prepared) (helpers : Helpers) {state : FinalState} {output : Iter}
    (trace : ExactLoopTrace (finalBody powers helpers) state output) :
    SliceAll GeneratedCanonicalQM31 state.1.iter.slice →
    BackAll GeneratedCanonicalQM31 state.2 →
    SliceAll GeneratedCanonicalQM31 output.iter.slice := by
  induction trace with
  | @done state output edge =>
      intro initial backCanonical
      unfold finalBody at edge
      unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0.body at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨⟨option, nextIter, nextBack⟩, nextRun, edge⟩ := edge
      cases option with
      | none =>
          have exactOutput := ControlFlow.done.inj (Result.ok.inj edge)
          rw [← exactOutput]
          exact backCanonical _ (enumerate_none_all GeneratedCanonicalQM31 _ _ _ nextRun initial)
      | some pair =>
          repeat' (rw [bind_eq_ok_iff] at edge; obtain ⟨_, _, edge⟩ := edge)
          cases edge
  | @cont state next output edge tail ih =>
      intro initial backCanonical
      unfold finalBody at edge
      unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0.body at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨⟨option, nextIter, nextBack⟩, nextRun, edge⟩ := edge
      cases option with
      | none => cases edge
      | some pair =>
          rcases pair with ⟨slot, oldValue⟩
          simp only at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨row0, row0Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨q0, q0Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨row1, row1Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨q1, q1Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨row2, row2Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨q2, q2Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨dot, dotRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨value, valueRun, edge⟩ := edge
          have facts := enumerate_some_all GeneratedCanonicalQM31 _ _ _ slot oldValue nextRun initial
          have dotCanonical := successful_prepared_sum_products3_canonical powers _ dot dotRun
          have valueCanonical := successful_result_property
            (callback_qm31_add_canonical oldValue dot facts.1 dotCanonical) valueRun
          have stateExact := ControlFlow.cont.inj (Result.ok.inj edge)
          apply ih
          · rw [← stateExact]
            exact facts.2.1
          · rw [← stateExact]
            intro candidate canonical
            apply backCanonical
            exact facts.2.2 _ valueCanonical candidate canonical

theorem successful_gamma_final_loop_canonical
    (powers : Prepared) (helpers : Helpers) (iter output : Iter)
    (back : Iter → Iter)
    (initial : SliceAll GeneratedCanonicalQM31 iter.iter.slice)
    (backCanonical : BackAll GeneratedCanonicalQM31 back)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0
      iter back powers helpers = ok output) :
    SliceAll GeneratedCanonicalQM31 output.iter.slice := by
  have loopRun : loop (finalBody powers helpers) (iter, back) = ok output := run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (finalBody powers helpers) (iter, back) output loopRun
  exact final_trace_canonical powers helpers trace initial backCanonical

private theorem population_done_canonical
    (toArray : Slice Helper → Helpers)
    (toSlice : core.slice.iter.IterMut Helper → Slice Helper)
    (toIter : HelperIter → core.slice.iter.IterMut Helper)
    (combined : Helper) (powers : Prepared) (c2 : Array Std.U32 48#usize)
    (iter : HelperIter) (back : HelperIter → HelperIter) (output : Helper)
    (canonical : SliceAll GeneratedCanonicalQM31 combined.to_slice)
    (edge : V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0.body
      toArray toSlice toIter combined powers c2 iter back = ok (done output)) :
    SliceAll GeneratedCanonicalQM31 output.to_slice := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨⟨option, nextIter, nextBack⟩, nextRun, edge⟩ := edge
  cases option with
  | none =>
      simp only [Array.to_slice_mut, Std.lift, core.slice.Slice.iter_mut,
        core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate, bind_tc_ok] at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨finished, finalRun, edge⟩ := edge
      have finishedCanonical := successful_gamma_final_loop_canonical powers _
        _ finished (fun e => e) canonical (fun _ h => h) finalRun
      have exactOutput := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← exactOutput]
      change SliceAll GeneratedCanonicalQM31 (Array.from_slice combined finished.iter.slice).to_slice
      unfold Array.from_slice
      split
      · exact finishedCanonical
      · exact canonical
  | some pair =>
      repeat' (rw [bind_eq_ok_iff] at edge; obtain ⟨_, _, edge⟩ := edge)
      cases edge

theorem successful_helper_population_canonical
    (toArray : Slice Helper → Helpers)
    (toSlice : core.slice.iter.IterMut Helper → Slice Helper)
    (toIter : HelperIter → core.slice.iter.IterMut Helper)
    (combined : Helper) (powers : Prepared) (c2 : Array Std.U32 48#usize)
    (iter : HelperIter) (back : HelperIter → HelperIter) (output : Helper)
    (canonical : SliceAll GeneratedCanonicalQM31 combined.to_slice)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0
      toArray toSlice toIter iter back combined powers c2 = ok output) :
    SliceAll GeneratedCanonicalQM31 output.to_slice := by
  let body := fun state : HelperIter × (HelperIter → HelperIter) =>
    V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0.body
      toArray toSlice toIter combined powers c2 state.1 state.2
  have loopRun : loop body (iter, back) = ok output := run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace body (iter, back) output loopRun
  generalize stateExact : (iter, back) = state at trace
  clear run loopRun stateExact
  induction trace with
  | done edge =>
      exact population_done_canonical toArray toSlice toIter combined powers c2 _ _ _ canonical edge
  | cont edge tail ih => exact ih

#print axioms successful_gamma_final_loop_canonical
#print axioms successful_helper_population_canonical
end V7ProductionCallbacksR30GammaHelpersCanonical
