import V7CallerCurrentReleaseR26QueryScaleExactStep
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Exact current R26 shifted query-scale loop

The source loop starts with `rho` at slot zero and fills slots one through
fifteen by one prepared multiplication each.  This file proves the complete
successful loop result symbolically from its body trace.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26QueryScaleExactLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26QueryScaleExactStep
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev ScaleState :=
  core.ops.range.Range Std.Usize × Array field.QM31 16#usize

local instance : Inhabited field.QM31 := ⟨field.QM31.ZERO⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- Literal values read and written by one continuing scale-loop edge. -/
structure ExactScaleStep
    (prepared : field.PreparedQm31Multiplier)
    (state nextState : ScaleState) : Type where
  ordinal : Std.Usize
  predecessor : Std.Usize
  prior : field.QM31
  next : field.QM31
  iteratorSuccess :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
      ok (some ordinal, nextState.1)
  predecessorSuccess :
    Std.Usize.wrapping_sub ordinal 1#usize = predecessor
  priorSuccess : state.2.index_usize predecessor = ok prior
  multiplySuccess :
    field.PreparedQm31Multiplier.impl.mul prepared prior = ok next
  updateSuccess : state.2.update ordinal next = ok nextState.2

private theorem continuing_body_exposes_step
    (prepared : field.PreparedQm31Multiplier)
    (state nextState : ScaleState)
    (edge :
      v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
        prepared state.1 state.2 = ok (cont nextState)) :
    Nonempty (ExactScaleStep prepared state nextState) := by
  rcases state with ⟨iter, scales⟩
  rcases nextState with ⟨iterNext, scalesNext⟩
  unfold v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, hiterator, edge⟩ := edge
  rcases iteratorPair with ⟨option, iteratorAfter⟩
  cases option with
  | none => cases edge
  | some ordinal =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨predecessor, hpredecessor, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨prior, hprior, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨next, hmultiply, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨updated, hupdate, edge⟩ := edge
      simp only [Aeneas.Std.Result.ok.injEq,
        Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq] at edge
      rcases edge with ⟨iteratorExact, updatedExact⟩
      subst iteratorAfter
      subst updated
      exact ⟨{
        ordinal := ordinal
        predecessor := predecessor
        prior := prior
        next := next
        iteratorSuccess := hiterator
        predecessorSuccess := by simpa [lift] using hpredecessor
        priorSuccess := hprior
        multiplySuccess := hmultiply
        updateSuccess := hupdate }⟩

private theorem finished_body_exposes_iterator
    (prepared : field.PreparedQm31Multiplier)
    (state : ScaleState) (output : Array field.QM31 16#usize)
    (edge :
      v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
        prepared state.1 state.2 = ok (done output)) :
    ∃ iterAfter,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
          ok (none, iterAfter) ∧
        output = state.2 := by
  rcases state with ⟨iter, scales⟩
  unfold v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, hiterator, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      exact ⟨iterAfter, hiterator,
        (ControlFlow.done.inj (Result.ok.inj edge)).symm⟩
  | some ordinal =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨predecessor, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨prior, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨next, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨updated, _, edge⟩ := edge
      cases edge

private theorem wrapping_sub_one_val
    (ordinal predecessor : Std.Usize)
    (positive : 1 ≤ ordinal.val)
    (run : Std.Usize.wrapping_sub ordinal 1#usize = predecessor) :
    predecessor.val + 1 = ordinal.val := by
  rw [← run]
  simp only [Std.Usize.wrapping_sub_val_eq]
  norm_num
  have hsize : ordinal.val < Usize.size := by
    simpa only [UScalar.size_UScalarTyUsize] using ordinal.hSize
  have rearrange :
      ordinal.val + (Usize.size - 1) =
        (ordinal.val - 1) + Usize.size := by omega
  rw [rearrange, Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem array_update_eq_set
    (values updated : Array field.QM31 16#usize)
    (index : Std.Usize) (value : field.QM31)
    (bound : index.val < 16)
    (run : values.update index value = ok updated) :
    updated = values.set index value := by
  have spec := Array.update_spec values index value (by
    simpa [Array.length_eq] using bound)
  obtain ⟨expected, expectedRun, expectedExact⟩ := WP.spec_imp_exists spec
  have outputExact : updated = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  exact outputExact.trans expectedExact

private theorem exact_scale_at_set_same
    (values : Array field.QM31 16#usize) (index : Std.Usize)
    (value : field.QM31) (bound : index.val < 16) :
    exactScaleAt (values.set index value) index.val =
      generatedQm31ToExact value := by
  unfold exactScaleAt
  rw [scale_array_set_same values index value bound]

private theorem exact_scale_at_set_ne
    (values : Array field.QM31 16#usize) (index : Std.Usize)
    (value : field.QM31) (other : Nat) (hne : other ≠ index.val) :
    exactScaleAt (values.set index value) other = exactScaleAt values other := by
  unfold exactScaleAt
  rw [scale_array_set_ne values index value other hne]

/-- One continuing source edge extends the exact shifted-power prefix by one
slot. -/
private theorem step_preserves_shifted_prefix
    (rho : field.QM31) (rhoExact : ExactQM31)
    (prepared : field.PreparedQm31Multiplier)
    (state nextState : ScaleState)
    (hrho : GeneratedCanonicalQM31 rho)
    (hrhoExact : generatedQm31ToExact rho = rhoExact)
    (hprepared : field.PreparedQm31Multiplier.impl.new rho = ok prepared)
    (hend : state.1.end.val = 16)
    (invariant : ShiftedScalePrefix rhoExact state.2 state.1.start)
    (step : ExactScaleStep prepared state nextState) :
    nextState.1.end.val = 16 ∧
      ShiftedScalePrefix rhoExact nextState.2 nextState.1.start := by
  obtain ⟨active, ordinalExact, nextStart, sameEnd⟩ :=
    range_next_some_exact state.1 nextState.1 step.ordinal
      step.iteratorSuccess
  have ordinalPositive : 1 ≤ step.ordinal.val := by
    rw [ordinalExact]
    exact invariant.2.1
  have ordinalBelow : step.ordinal.val < 16 := by
    rw [ordinalExact]
    omega
  have ordinalValExact : step.ordinal.val = state.1.start.val :=
    congrArg UScalar.val ordinalExact
  have predecessorNext : step.predecessor.val + 1 = step.ordinal.val :=
    wrapping_sub_one_val step.ordinal step.predecessor ordinalPositive
      step.predecessorSuccess
  have predecessorBelow : step.predecessor.val < state.1.start.val := by
    rw [← ordinalExact, ← predecessorNext]
    omega
  have priorRaw : state.2.val[step.predecessor.val]! = step.prior := by
    have valueSome : state.2.val[step.predecessor.val]? = some step.prior := by
      have hprior := step.priorSuccess
      unfold Array.index_usize at hprior
      cases hvalue : state.2[step.predecessor]? with
      | none => simp [hvalue] at hprior
      | some value =>
          simp only [hvalue] at hprior
          have valueExact := Result.ok.inj hprior
          subst value
          simpa using hvalue
    exact List.getElem!_of_getElem? valueSome
  have priorCanonical : GeneratedCanonicalQM31 step.prior := by
    rw [← priorRaw]
    exact invariant.1 step.predecessor.val
      (lt_of_lt_of_le predecessorBelow invariant.2.2.1)
  obtain ⟨nextCanonical, nextExact, _⟩ :=
    scale_loop_body_step_exact rho step.prior step.next prepared state.1
      nextState.1 state.2 nextState.2 step.ordinal step.predecessor hrho
      priorCanonical hprepared step.iteratorSuccess step.predecessorSuccess
      step.priorSuccess step.multiplySuccess step.updateSuccess
  have priorExact : generatedQm31ToExact step.prior =
      rhoExact ^ step.ordinal.val := by
    have fromPrefix := invariant.2.2.2 step.predecessor.val predecessorBelow
    unfold exactScaleAt at fromPrefix
    rw [priorRaw] at fromPrefix
    rw [predecessorNext] at fromPrefix
    exact fromPrefix
  have nextPower : generatedQm31ToExact step.next =
      rhoExact ^ (step.ordinal.val + 1) := by
    rw [nextExact, hrhoExact, priorExact]
    rw [pow_succ']
  have updatedExact : nextState.2 = state.2.set step.ordinal step.next :=
    array_update_eq_set state.2 nextState.2 step.ordinal step.next
      ordinalBelow step.updateSuccess
  constructor
  · rw [sameEnd, hend]
  · rw [updatedExact]
    refine ⟨canonical_scale_array_set state.2 step.ordinal step.next
      ordinalBelow invariant.1 nextCanonical, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro index indexBelow
      by_cases same : index = step.ordinal.val
      · subst index
        rw [exact_scale_at_set_same state.2 step.ordinal step.next
          ordinalBelow, nextPower]
      · have oldIndex : index < state.1.start.val := by
          omega
        rw [exact_scale_at_set_ne state.2 step.ordinal step.next index same]
        exact invariant.2.2.2 index oldIndex

private theorem exact_trace_finishes_shifted_prefix
    (rho : field.QM31) (rhoExact : ExactQM31)
    (prepared : field.PreparedQm31Multiplier)
    (hrho : GeneratedCanonicalQM31 rho)
    (hrhoExact : generatedQm31ToExact rho = rhoExact)
    (hprepared : field.PreparedQm31Multiplier.impl.new rho = ok prepared) :
    ∀ {state output},
      ExactLoopTrace
        (fun state : ScaleState =>
          v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
            prepared state.1 state.2)
        state output →
      state.1.end.val = 16 →
      ShiftedScalePrefix rhoExact state.2 state.1.start →
      ShiftedScalePrefix rhoExact output 16#usize := by
  intro state output execution hend invariant
  cases execution with
  | done edge =>
      obtain ⟨iterAfter, iteratorRun, outputExact⟩ :=
        finished_body_exposes_iterator prepared state output edge
      have exhausted := range_next_none_exhausted state.1 iterAfter iteratorRun
      have startUpper := invariant.2.2.1
      have startValExact : state.1.start.val = 16 := by omega
      have startExact : state.1.start = 16#usize := by
        apply UScalar.eq_of_val_eq
        exact startValExact
      subst output
      rw [startExact] at invariant
      exact invariant
  | @cont _ nextState _ edge tail =>
      obtain ⟨step⟩ := continuing_body_exposes_step prepared state nextState edge
      obtain ⟨nextEnd, nextPrefix⟩ := step_preserves_shifted_prefix rho
        rhoExact prepared state nextState hrho hrhoExact hprepared hend invariant step
      exact exact_trace_finishes_shifted_prefix rho rhoExact prepared hrho
        hrhoExact hprepared tail nextEnd nextPrefix

/-- A successful literal scale loop produces the complete shifted covector
`rho, rho^2, ..., rho^16`. -/
theorem successful_scale_loop_has_exact_shifted_powers
    (rho : field.QM31) (rhoExact : ExactQM31)
    (prepared : field.PreparedQm31Multiplier)
    (seed scales : Array field.QM31 16#usize)
    (hrho : GeneratedCanonicalQM31 rho)
    (hrhoExact : generatedQm31ToExact rho = rhoExact)
    (hseed : Array.update (Array.repeat 16#usize field.QM31.ZERO)
      0#usize rho = ok seed)
    (hprepared : field.PreparedQm31Multiplier.impl.new rho = ok prepared)
    (run :
      v6_query_batch.add_final256_query_batch_with_initial_scale_loop
        { start := 1#usize, «end» := v6_query_batch.V6_QUERY_BATCH_COUNT }
        seed prepared = ok scales) :
    ShiftedScalePrefix rhoExact scales 16#usize := by
  unfold v6_query_batch.add_final256_query_batch_with_initial_scale_loop at run
  obtain ⟨execution⟩ := loop_success_yields_exact_trace
    (fun state : ScaleState =>
      v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
        prepared state.1 state.2)
    ({ start := 1#usize, «end» := v6_query_batch.V6_QUERY_BATCH_COUNT }, seed)
    scales run
  apply exact_trace_finishes_shifted_prefix rho rhoExact prepared hrho
    hrhoExact hprepared execution
  · simp [v6_query_batch.V6_QUERY_BATCH_COUNT]
  · exact shifted_scale_seed_prefix rho seed rhoExact hrho hrhoExact hseed

end V7CallerCurrentReleaseR26QueryScaleExactLoop
