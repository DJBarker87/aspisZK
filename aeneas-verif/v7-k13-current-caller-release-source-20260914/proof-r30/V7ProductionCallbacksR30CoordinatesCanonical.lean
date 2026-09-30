import V7ProductionCallbacksR30CirclePointCanonical
import V7ProductionCallbacksR29.FunsChunk45
import V7ProductionSnapshotObserverR28.Funs

/-!
# Canonicality of current production V6 query coordinates

This module follows the callback after circle-point selection and proves that
its returned line coordinates retain the base-field representation invariant.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30CoordinatesCanonical

open V7ProductionCallbacksR30FieldCanonical
open V7ProductionCallbacksR30CirclePointCanonical
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev Point := V7ProductionCallbacksR29.aspis_core.circle_fri.BaseCirclePoint
abbrev M31 := V7ProductionCallbacksR29.aspis_core.field.M31

local instance : Inhabited Point :=
  ⟨{ x := V7ProductionCallbacksR29.aspis_core.field.M31.ZERO,
     y := V7ProductionCallbacksR29.aspis_core.field.M31.ZERO }⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem point_index_canonical
    (points : alloc.vec.Vec Point) (index : Std.Usize) (point : Point)
    (canonical : PointsCanonical points)
    (run : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Point) points index = ok point) :
    PointCanonical point := by
  rw [alloc.vec.Vec.index_slice_index] at run
  unfold alloc.vec.Vec.index_usize at run
  split at run
  · cases run
  · rename_i present
    have presentList : points.val[index.val]? = some point := by
      simpa [Result.ok.inj run] using present
    have bound : index.val < points.val.length := by
      by_contra outOfBounds
      have absent : points.val[index.val]? = none :=
        List.getElem?_eq_none (by omega)
      rw [absent] at presentList
      cases presentList
    have exact : point = points.val[index.val]! := by
      symm
      exact List.getElem!_of_getElem? presentList
    rw [exact]
    rw [← List.Inhabited_getElem_eq_getElem! points.val index.val bound]
    exact canonical _ (List.getElem_mem bound)

private theorem successful_m31_mul_canonical
    (left right output : M31)
    (leftCanonical : AspisAeneasCM31Multiplicative.CanonicalRawM31 left.val)
    (rightCanonical : AspisAeneasCM31Multiplicative.CanonicalRawM31 right.val)
    (run : V7ProductionCallbacksR29.aspis_core.field.M31.mul left right = ok output) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  obtain ⟨expected, expectedRun, expectedCanonical⟩ :=
    callback_m31_mul_canonical left right leftCanonical rightCanonical
  have outputExact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [outputExact]
  exact expectedCanonical

private theorem successful_m31_double_canonical
    (value output : M31)
    (valueCanonical : AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val)
    (run : V7ProductionCallbacksR29.aspis_core.field.M31.double value = ok output) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  obtain ⟨expected, expectedRun, expectedCanonical⟩ :=
    callback_m31_double_canonical value valueCanonical
  have outputExact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [outputExact]
  exact expectedCanonical

private theorem successful_m31_sub_canonical
    (left right output : M31)
    (leftCanonical : AspisAeneasCM31Multiplicative.CanonicalRawM31 left.val)
    (rightCanonical : AspisAeneasCM31Multiplicative.CanonicalRawM31 right.val)
    (run : V7ProductionCallbacksR29.aspis_core.field.M31.sub left right = ok output) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  obtain ⟨expected, expectedRun, expectedCanonical⟩ :=
    callback_m31_sub_canonical left right leftCanonical rightCanonical
  have outputExact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [outputExact]
  exact expectedCanonical

private theorem one_canonical :
    AspisAeneasCM31Multiplicative.CanonicalRawM31
      V7ProductionCallbacksR29.aspis_core.field.M31.ONE.val := by
  norm_num [V7ProductionCallbacksR29.aspis_core.field.M31.ONE,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

theorem closure3_output_canonical
    (points : alloc.vec.Vec Point) (index : Std.Usize)
    (output : M31) (state : alloc.vec.Vec Point)
    (pointsCanonical : PointsCanonical points)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut points index =
      ok (output, state)) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
    at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨point, pointRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨squared, squaredRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨doubled, doubledRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨result, resultRun, run⟩ := run
  have pointCanonical := point_index_canonical points index point pointsCanonical pointRun
  have squaredCanonical := successful_m31_mul_canonical point.x point.x squared
    pointCanonical.1 pointCanonical.1 squaredRun
  have doubledCanonical := successful_m31_double_canonical squared doubled
    squaredCanonical doubledRun
  have resultCanonical := successful_m31_sub_canonical doubled
    V7ProductionCallbacksR29.aspis_core.field.M31.ONE result doubledCanonical
    one_canonical resultRun
  have outputExact : output = result := by
    exact (congrArg Prod.fst (Result.ok.inj run)).symm
  rw [outputExact]
  exact resultCanonical

private theorem closure3_state_exact
    (points : alloc.vec.Vec Point) (index : Std.Usize)
    (output : M31) (state : alloc.vec.Vec Point)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut points index =
      ok (output, state)) :
    state = points := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
    at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨point, pointRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨squared, squaredRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨doubled, doubledRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨result, resultRun, run⟩ := run
  exact (congrArg Prod.snd (Result.ok.inj run)).symm

private theorem usize_add_one_ok (low next : Std.Usize)
    (valueExact : low.val + 1 = next.val) :
    low + 1#usize = (ok next : Result Std.Usize) := by
  have bound : low.val + 1 < 2 ^ System.Platform.numBits := by
    rw [valueExact]
    exact next.hBounds
  have addSpec := @UScalar.add_equiv UScalarTy.Usize low 1#usize
  generalize runEq : (low + 1#usize) = result at addSpec ⊢
  cases result with
  | fail error =>
      exfalso
      apply addSpec
      simpa using bound
  | div => exact False.elim addSpec
  | ok value =>
      have sameValue : value.val = next.val := by
        calc
          value.val = low.val + (1#usize).val := addSpec.2.1
          _ = low.val + 1 := by rfl
          _ = next.val := valueExact
      have exact : value = next := UScalar.val_eq_imp value next sameValue
      simp [exact]

def LineCanonical (line : Array M31 16#usize) : Prop :=
  ∀ ordinal, ordinal < 16 →
    AspisAeneasCM31Multiplicative.CanonicalRawM31 line.val[ordinal]!.val

private theorem from_fn_list_canonical
    (fuel : Nat) (index : Std.Usize) (points : alloc.vec.Vec Point)
    (values : List M31) (finalState : alloc.vec.Vec Point)
    (pointsCanonical : PointsCanonical points)
    (run : core.array.fromFnList
      V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      fuel index points = ok (values, finalState)) :
    ∀ value ∈ values,
      AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val := by
  induction fuel generalizing index values finalState with
  | zero =>
      rw [core.array.fromFnList.eq_1] at run
      have valuesEmpty : values = [] :=
        (congrArg Prod.fst (Result.ok.inj run)).symm
      rw [valuesEmpty]
      simp
  | succ fuel inductionHypothesis =>
      cases fuel with
      | zero =>
          rw [core.array.fromFnList.eq_2] at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨callResult, callRun, run⟩ := run
          rcases callResult with ⟨value, nextState⟩
          have valuesExact : values = [value] :=
            (congrArg Prod.fst (Result.ok.inj run)).symm
          rw [valuesExact]
          intro target targetInValues
          simp only [List.mem_cons, List.not_mem_nil, or_false] at targetInValues
          rw [targetInValues]
          exact closure3_output_canonical points index value nextState
            pointsCanonical callRun
      | succ remaining =>
          rw [core.array.fromFnList.eq_2] at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨callResult, callRun, run⟩ := run
          rcases callResult with ⟨value, nextState⟩
          rw [bind_eq_ok_iff] at run
          obtain ⟨nextIndex, indexRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨tailResult, tailRun, run⟩ := run
          rcases tailResult with ⟨tail, tailState⟩
          have nextStateExact : nextState = points :=
            closure3_state_exact points index value nextState callRun
          rw [nextStateExact] at tailRun
          have tailCanonical := inductionHypothesis nextIndex tail tailState tailRun
          have valuesExact : values = value :: tail :=
            (congrArg Prod.fst (Result.ok.inj run)).symm
          rw [valuesExact]
          intro target targetInValues
          simp only [List.mem_cons] at targetInValues
          rcases targetInValues with targetExact | targetInTail
          · rw [targetExact]
            exact closure3_output_canonical points index value nextState
              pointsCanonical callRun
          · exact tailCanonical target targetInTail

theorem line_from_fn_canonical
    (points : alloc.vec.Vec Point) (line : Array M31 16#usize)
    (pointsCanonical : PointsCanonical points)
    (run : core.array.from_fn 16#usize
      V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      points = ok line) :
    LineCanonical line := by
  unfold core.array.from_fn at run
  have sixteenVal : (16#usize).val = 16 := rfl
  simp only [sixteenVal] at run
  generalize listRun : core.array.fromFnList
    V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31
    16 0#usize points = computation at run
  cases computation with
  | fail error => simp at run
  | div => simp at run
  | ok pair =>
      rcases pair with ⟨values, finalState⟩
      dsimp at run
      split at run
      · rename_i valuesLength
        have lineExact : line.val = values := by
          exact congrArg Subtype.val (Result.ok.inj run).symm
        have valuesCanonical := from_fn_list_canonical 16 0#usize points
          values finalState pointsCanonical listRun
        intro ordinal ordinalBound
        rw [lineExact]
        have valueBound : ordinal < values.length := by omega
        rw [← List.Inhabited_getElem_eq_getElem! values ordinal valueBound]
        exact valuesCanonical _ (List.getElem_mem valueBound)
      · cases run

private abbrev PrepareIter := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.Iter Point)

private abbrev PrepareState := PrepareIter × Array M31 32#usize

private def prepareBody (points : alloc.vec.Vec Point) (state : PrepareState) :
    Result (ControlFlow PrepareState
      (core.result.Result
        V7ProductionCallbacksR29.aspis_core.v6_onefold.V6OneFoldCoordinates
        V7ProductionCallbacksR29.aspis_core.v6_onefold.V6WireError)) :=
  V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop.body
    points state.1 state.2

private theorem prepare_body_done_line_canonical
    (points : alloc.vec.Vec Point) (state : PrepareState)
    (coordinates : V7ProductionCallbacksR29.aspis_core.v6_onefold.V6OneFoldCoordinates)
    (edge : prepareBody points state = ok (done (.Ok coordinates)))
    (pointsCanonical : PointsCanonical points) :
    LineCanonical coordinates.line_x := by
  rcases state with ⟨iter, denominators⟩
  unfold prepareBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop.body
    at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨denominatorSlice, denominatorSliceRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨inverseSlicePair, inverseSliceRun, edge⟩ := edge
      rcases inverseSlicePair with ⟨inverseSlice, inverseSliceBack⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨inverseSliceResult, inverseBatchRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨m, mRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨m1, m1Run, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨m2, m2Run, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨nonUnit, nonUnitRun, edge⟩ := edge
      by_cases nonUnitIsTrue : nonUnit
      · simp [nonUnitIsTrue] at edge
      · simp [nonUnitIsTrue] at edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨inverseX, inverseXRun, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨inverseY, inverseYRun, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨lineX, lineXRun, edge⟩ := edge
        have coordinatesExact : coordinates =
            { inv_2x := inverseX, inv_2y := inverseY, line_x := lineX } := by
          exact (core.result.Result.Ok.inj
            (ControlFlow.done.inj (Result.ok.inj edge))).symm
        rw [coordinatesExact]
        exact line_from_fn_canonical points lineX pointsCanonical lineXRun
  | some point =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨x, xRun, edge⟩ := edge
      repeat' first
        | rw [bind_eq_ok_iff] at edge
        | obtain ⟨_, _, edge⟩ := edge
        | split at edge

private theorem prepare_trace_line_canonical
    (points : alloc.vec.Vec Point) {state : PrepareState}
    {output : core.result.Result
      V7ProductionCallbacksR29.aspis_core.v6_onefold.V6OneFoldCoordinates
      V7ProductionCallbacksR29.aspis_core.v6_onefold.V6WireError}
    (trace : ExactLoopTrace (prepareBody points) state output)
    (pointsCanonical : PointsCanonical points) :
    ∀ coordinates, output = .Ok coordinates → LineCanonical coordinates.line_x := by
  induction trace with
  | @done state output edge =>
      intro coordinates outputExact
      cases outputExact
      exact prepare_body_done_line_canonical points state coordinates edge
        pointsCanonical
  | @cont state next output edge tail inductionHypothesis =>
      intro coordinates outputExact
      exact inductionHypothesis coordinates outputExact

theorem successful_prepare_v6_onefold_coordinates_loop_line_canonical
    (iter : PrepareIter) (points : alloc.vec.Vec Point)
    (denominators : Array M31 32#usize)
    (coordinates : V7ProductionCallbacksR29.aspis_core.v6_onefold.V6OneFoldCoordinates)
    (pointsCanonical : PointsCanonical points)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop
      iter points denominators = ok (.Ok coordinates)) :
    LineCanonical coordinates.line_x := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop
    at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (prepareBody points)
    (iter, denominators) (.Ok coordinates) run
  exact prepare_trace_line_canonical points trace pointsCanonical coordinates rfl

theorem successful_prepare_v6_onefold_coordinates_line_canonical
    (queries : Array Std.U32 16#usize)
    (coordinates : V7ProductionCallbacksR29.aspis_core.v6_onefold.V6OneFoldCoordinates)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates
      queries = ok (.Ok coordinates)) :
    LineCanonical coordinates.line_x := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.prepare_v6_onefold_coordinates
    at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨querySlice, querySliceRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨selectedResult, selectedRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨mappedResult, mappedRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨branchResult, branchRun, run⟩ := run
  cases selectedResult with
  | Ok points =>
      have querySliceExact : querySlice = Array.to_slice queries :=
        (Result.ok.inj querySliceRun).symm
      rw [querySliceExact] at selectedRun
      have pointsCanonical : PointsCanonical points :=
        successful_selected_v6_points_canonical queries points selectedRun
      have mappedExact : mappedResult = .Ok points := by
        simpa [core.result.Result.map_err] using (Result.ok.inj mappedRun).symm
      rw [mappedExact] at branchRun
      have branchExact : branchResult = .Continue points := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj branchRun).symm
      rw [branchExact] at run
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨iterator, iteratorRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨enumerated, enumerateRun, run⟩ := run
      exact successful_prepare_v6_onefold_coordinates_loop_line_canonical
        enumerated points
        (Array.repeat 32#usize V7ProductionCallbacksR29.aspis_core.field.M31.ZERO)
        coordinates pointsCanonical run
  | Err error =>
      simp only [core.result.Result.map_err] at mappedRun
      rw [bind_eq_ok_iff] at mappedRun
      obtain ⟨mappedError, mapRun, mappedRun⟩ := mappedRun
      have mappedExact : mappedResult = .Err mappedError :=
        (Result.ok.inj mappedRun).symm
      rw [mappedExact] at branchRun
      have branchExact : branchResult = .Break (.Err mappedError) := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj branchRun).symm
      rw [branchExact] at run
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run

theorem successful_authenticate_and_fold_queries_line_canonical
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : V7ProductionCallbacksR29.aspis_core.v7_onefold.V7CompactOneFoldWire)
    (view : V7ProductionCallbacksR29.aspis_core.v6_transcript.V6QueryBatchView)
    (authenticated : V7ProductionCallbacksR29.aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
    (run : V7ProductionCallbacksR29.v7_verifier.authenticate_and_fold_queries
      hash wire view = ok (.Ok authenticated)) :
    LineCanonical authenticated.line_x := by
  unfold V7ProductionCallbacksR29.v7_verifier.authenticate_and_fold_queries at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateResult, coordinateRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateBranch, coordinateBranchRun, run⟩ := run
  cases coordinateResult with
  | Ok coordinates =>
      have coordinatesCanonical :=
        successful_prepare_v6_onefold_coordinates_line_canonical
          view.queries coordinates coordinateRun
      have coordinateBranchExact : coordinateBranch = .Continue coordinates := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedResult, combinedRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedBranch, combinedBranchRun, run⟩ := run
      cases combinedResult with
      | Ok combined =>
          have combinedBranchExact : combinedBranch = .Continue combined := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨folded, foldedRun, run⟩ := run
          have authenticatedExact : authenticated =
              { values := folded, line_x := coordinates.line_x } := by
            exact (core.result.Result.Ok.inj (Result.ok.inj run)).symm
          rw [authenticatedExact]
          exact coordinatesCanonical
      | Err error =>
          have combinedBranchExact : combinedBranch = .Break (.Err error) := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Err error =>
      have coordinateBranchExact : coordinateBranch = .Break (.Err error) := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run

/-- The production observer uses the callback implementation above through
its generated external binding.  This theorem follows the observer's literal
wrapper, retaining the canonical source-coordinate line at its query-fold
boundary. -/
theorem successful_production_observer_authenticate_and_fold_queries_line_canonical
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
    (view : V7ProductionSnapshotObserverR28.aspis_core.v6_transcript.V6QueryBatchView)
    (authenticated : V7ProductionSnapshotObserverR28.aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
    (run : V7ProductionSnapshotObserverR28.v7_verifier.authenticate_and_fold_queries
      hash wire view = ok (.Ok authenticated)) :
    LineCanonical authenticated.line_x := by
  unfold V7ProductionSnapshotObserverR28.v7_verifier.authenticate_and_fold_queries at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateResult, coordinateRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateBranch, coordinateBranchRun, run⟩ := run
  cases coordinateResult with
  | Ok coordinates =>
      have coordinatesCanonical :=
        successful_prepare_v6_onefold_coordinates_line_canonical
          view.queries coordinates coordinateRun
      have coordinateBranchExact : coordinateBranch = .Continue coordinates := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedResult, combinedRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedBranch, combinedBranchRun, run⟩ := run
      cases combinedResult with
      | Ok combined =>
          have combinedBranchExact : combinedBranch = .Continue combined := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨folded, foldedRun, run⟩ := run
          have authenticatedExact : authenticated =
              { values := folded, line_x := coordinates.line_x } := by
            exact (core.result.Result.Ok.inj (Result.ok.inj run)).symm
          rw [authenticatedExact]
          exact coordinatesCanonical
      | Err error =>
          have combinedBranchExact : combinedBranch = .Break (.Err error) := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Err error =>
      have coordinateBranchExact : coordinateBranch = .Break (.Err error) := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run

theorem successful_production_observer_query_fold_line_canonical
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
    (view : V7ProductionSnapshotObserverR28.aspis_core.v6_transcript.V6QueryBatchView)
    (authenticated : V7ProductionSnapshotObserverR28.aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
    (run : V7ProductionSnapshotObserverR28.v7_verifier.observe_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError.call_once
      (hash, wire) view = ok (.Ok authenticated)) :
    LineCanonical authenticated.line_x := by
  change V7ProductionSnapshotObserverR28.v7_verifier.authenticate_and_fold_queries
    hash wire view = ok (.Ok authenticated) at run
  exact successful_production_observer_authenticate_and_fold_queries_line_canonical
    hash wire view authenticated run

#print axioms closure3_output_canonical
#print axioms line_from_fn_canonical
#print axioms successful_prepare_v6_onefold_coordinates_line_canonical
#print axioms successful_production_observer_authenticate_and_fold_queries_line_canonical
#print axioms successful_production_observer_query_fold_line_canonical

end V7ProductionCallbacksR30CoordinatesCanonical
