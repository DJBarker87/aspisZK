import V7ProductionCallbacksR30FieldCanonical
import V7ProductionCallbacksR30CircleTableCanonical
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Canonicality of production V6 circle points

The fixed circle-table certificate supplies canonical coordinates at every
lookup.  This module proves that the exact generated point-addition routine
preserves those bounds.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30CirclePointCanonical

open V7ProductionCallbacksR30FieldCanonical
open V7ProductionCallbacksR30CircleTableCanonical
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev Point := V7ProductionCallbacksR29.aspis_core.circle_fri.BaseCirclePoint

def PointCanonical (point : Point) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 point.x.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 point.y.val

theorem callback_base_point_add_canonical
    (left right output : Point)
    (leftCanonical : PointCanonical left)
    (rightCanonical : PointCanonical right)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.BaseCirclePoint.add
      left right = ok output) :
    PointCanonical output := by
  obtain ⟨m0, hm0, hm0Canonical⟩ :=
    callback_m31_mul_canonical left.x right.x leftCanonical.1 rightCanonical.1
  obtain ⟨m1, hm1, hm1Canonical⟩ :=
    callback_m31_mul_canonical left.y right.y leftCanonical.2 rightCanonical.2
  obtain ⟨m2, hm2, hm2Canonical⟩ :=
    callback_m31_sub_canonical m0 m1 hm0Canonical hm1Canonical
  obtain ⟨m3, hm3, hm3Canonical⟩ :=
    callback_m31_mul_canonical left.x right.y leftCanonical.1 rightCanonical.2
  obtain ⟨m4, hm4, hm4Canonical⟩ :=
    callback_m31_mul_canonical left.y right.x leftCanonical.2 rightCanonical.1
  obtain ⟨m5, hm5, hm5Canonical⟩ :=
    callback_m31_add_canonical m3 m4 hm3Canonical hm4Canonical
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.BaseCirclePoint.add at run
  simp only [hm0, bind_tc_ok, hm1, hm2, hm3, hm4, hm5] at run
  have outputExact : output = { x := m2, y := m5 } := by
    exact Result.ok.inj run |>.symm
  rw [outputExact]
  exact ⟨hm2Canonical, hm5Canonical⟩

private theorem pair_zero_canonical
    (pair : Array Std.U32 2#usize) (value : Std.U32)
    (canonical : PairCanonical pair)
    (run : Array.index_usize pair 0#usize = ok value) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i present
    have exact : value = pair.val[0]! := by
      symm
      exact List.getElem!_of_getElem? (by simpa [Result.ok.inj run] using present)
    rw [exact]
    exact canonical.1

private theorem pair_one_canonical
    (pair : Array Std.U32 2#usize) (value : Std.U32)
    (canonical : PairCanonical pair)
    (run : Array.index_usize pair 1#usize = ok value) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i present
    have exact : value = pair.val[1]! := by
      symm
      exact List.getElem!_of_getElem? (by simpa [Result.ok.inj run] using present)
    rw [exact]
    exact canonical.2

def PointsCanonical (points : alloc.vec.Vec Point) : Prop :=
  ∀ point ∈ points.val, PointCanonical point

private theorem points_canonical_append
    (points : alloc.vec.Vec Point) (point : Point)
    (pointsCanonical : PointsCanonical points)
    (pointCanonical : PointCanonical point) :
    ∀ output : alloc.vec.Vec Point,
      alloc.vec.Vec.push points point = ok output → PointsCanonical output := by
  intro output run
  unfold alloc.vec.Vec.push at run
  simp only at run
  split at run
  · have valuesExact : output.val = points.val ++ [point] := by
      simpa [List.concat_eq_append] using
        congrArg Subtype.val (Result.ok.inj run).symm
    unfold PointsCanonical
    intro entry member
    rw [valuesExact] at member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact pointsCanonical entry member
    · exact pointCanonical
  · cases run

private theorem low_point_canonical
    (index : Std.Usize) (pair : Array Std.U32 2#usize)
    (x y : Std.U32)
    (tableRun : Array.index_usize
      V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_LOW6_WINDOW
      index = ok pair)
    (xRun : Array.index_usize pair 0#usize = ok x)
    (yRun : Array.index_usize pair 1#usize = ok y) :
    PointCanonical ({ x := x, y := y } : Point) := by
  exact ⟨pair_zero_canonical pair x (low6_lookup_canonical index pair tableRun) xRun,
    pair_one_canonical pair y (low6_lookup_canonical index pair tableRun) yRun⟩

private theorem middle_point_canonical
    (index : Std.Usize) (pair : Array Std.U32 2#usize)
    (x y : Std.U32)
    (tableRun : Array.index_usize
      V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_MIDDLE6_WINDOW
      index = ok pair)
    (xRun : Array.index_usize pair 0#usize = ok x)
    (yRun : Array.index_usize pair 1#usize = ok y) :
    PointCanonical ({ x := x, y := y } : Point) := by
  exact ⟨pair_zero_canonical pair x (middle6_lookup_canonical index pair tableRun) xRun,
    pair_one_canonical pair y (middle6_lookup_canonical index pair tableRun) yRun⟩

private theorem high_point_canonical
    (index : Std.Usize) (pair : Array Std.U32 2#usize)
    (x y : Std.U32)
    (tableRun : Array.index_usize
      V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_HIGH6_WINDOW
      index = ok pair)
    (xRun : Array.index_usize pair 0#usize = ok x)
    (yRun : Array.index_usize pair 1#usize = ok y) :
    PointCanonical ({ x := x, y := y } : Point) := by
  exact ⟨pair_zero_canonical pair x (high6_lookup_canonical index pair tableRun) xRun,
    pair_one_canonical pair y (high6_lookup_canonical index pair tableRun) yRun⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

abbrev FiberIter := core.slice.iter.Iter Std.U32
abbrev FiberState := FiberIter × alloc.vec.Vec Point

private def v6FiberBody (fiberCount : Std.Usize) (state : FiberState) :
    Result (ControlFlow FiberState
      (core.result.Result (alloc.vec.Vec Point)
        V7ProductionCallbacksR29.aspis_core.circle_fri.CircleFriError)) :=
  V7ProductionCallbacksR29.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1.body
    fiberCount state.1 state.2

private theorem v6_fiber_body_cont_preserves
    (fiberCount : Std.Usize) (state next : FiberState)
    (edge : v6FiberBody fiberCount state = ok (cont next))
    (canonical : PointsCanonical state.2) :
    PointsCanonical next.2 := by
  rcases state with ⟨iter, points⟩
  rcases next with ⟨iterNext, pointsNext⟩
  unfold v6FiberBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1.body
    at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some fiber =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨i, iRun, edge⟩ := edge
      by_cases inRange : i >= fiberCount
      · simp [inRange] at edge
      · simp [inRange] at edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨i1, i1Run, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨i2, i2Run, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨i3, i3Run, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨natural, naturalRun, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨i4, i4Run, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨lowPair, lowPairRun, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨lowX, lowXRun, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨lowY, lowYRun, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨i5, i5Run, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨middleIndex, middleIndexRun, edge⟩ := edge
        have lowCanonical := low_point_canonical i4 lowPair lowX lowY
          lowPairRun lowXRun lowYRun
        by_cases middleZero : middleIndex.val = 0
        · simp [middleZero] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨highIndex, highIndexRun, edge⟩ := edge
          by_cases highZero : highIndex.val = 0
          · simp [highZero] at edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨pushed, pushRun, edge⟩ := edge
            have outputExact : pointsNext = pushed := by
              exact (congrArg Prod.snd
                (ControlFlow.cont.inj (Result.ok.inj edge))).symm
            rw [outputExact]
            exact points_canonical_append points { x := lowX, y := lowY }
              canonical lowCanonical pushed pushRun
          · simp [highZero] at edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨highPair, highPairRun, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨highX, highXRun, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨highY, highYRun, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨point1, point1Run, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨pushed, pushRun, edge⟩ := edge
            have highCanonical := high_point_canonical highIndex highPair highX highY
              highPairRun highXRun highYRun
            have point1Canonical := callback_base_point_add_canonical
              { x := lowX, y := lowY } { x := highX, y := highY } point1
              lowCanonical highCanonical point1Run
            have outputExact : pointsNext = pushed := by
              exact (congrArg Prod.snd
                (ControlFlow.cont.inj (Result.ok.inj edge))).symm
            rw [outputExact]
            exact points_canonical_append points point1 canonical point1Canonical
              pushed pushRun
        · simp [middleZero] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨middlePair, middlePairRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨middleX, middleXRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨middleY, middleYRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨point, pointRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨highIndex, highIndexRun, edge⟩ := edge
          have middleCanonical :=
            middle_point_canonical middleIndex middlePair middleX middleY
              middlePairRun middleXRun middleYRun
          have pointCanonical := callback_base_point_add_canonical
            { x := lowX, y := lowY } { x := middleX, y := middleY } point
            lowCanonical middleCanonical pointRun
          by_cases highZero : highIndex.val = 0
          · simp [highZero] at edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨pushed, pushRun, edge⟩ := edge
            have outputExact : pointsNext = pushed := by
              exact (congrArg Prod.snd
                (ControlFlow.cont.inj (Result.ok.inj edge))).symm
            rw [outputExact]
            exact points_canonical_append points point canonical pointCanonical
              pushed pushRun
          · simp [highZero] at edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨highPair, highPairRun, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨highX, highXRun, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨highY, highYRun, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨point1, point1Run, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨pushed, pushRun, edge⟩ := edge
            have highCanonical := high_point_canonical highIndex highPair highX highY
              highPairRun highXRun highYRun
            have point1Canonical := callback_base_point_add_canonical point
              { x := highX, y := highY } point1 pointCanonical highCanonical point1Run
            have outputExact : pointsNext = pushed := by
              exact (congrArg Prod.snd
                (ControlFlow.cont.inj (Result.ok.inj edge))).symm
            rw [outputExact]
            exact points_canonical_append points point1 canonical point1Canonical
              pushed pushRun

private theorem v6_fiber_body_done_canonical
    (fiberCount : Std.Usize) (state : FiberState) (output : alloc.vec.Vec Point)
    (edge : v6FiberBody fiberCount state = ok (done (.Ok output)))
    (canonical : PointsCanonical state.2) :
    PointsCanonical output := by
  rcases state with ⟨iter, points⟩
  unfold v6FiberBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1.body
    at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
      simp only [core.result.Result.Ok.injEq] at outputExact
      rw [← outputExact]
      exact canonical
  | some fiber =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨i, iRun, edge⟩ := edge
      by_cases inRange : i >= fiberCount
      · simp [inRange] at edge
      · simp [inRange] at edge
        repeat' first
          | rw [bind_eq_ok_iff] at edge
          | obtain ⟨_, _, edge⟩ := edge
          | split at edge

private theorem v6_fiber_trace_canonical
    (fiberCount : Std.Usize) {state : FiberState}
    {output : core.result.Result (alloc.vec.Vec Point)
      V7ProductionCallbacksR29.aspis_core.circle_fri.CircleFriError}
    (trace : ExactLoopTrace (v6FiberBody fiberCount) state output)
    (canonical : PointsCanonical state.2) :
    ∀ points, output = .Ok points → PointsCanonical points := by
  induction trace with
  | @done state output edge =>
      intro points outputExact
      cases outputExact
      exact v6_fiber_body_done_canonical fiberCount state points edge canonical
  | @cont state next output edge tail inductionHypothesis =>
      intro points outputExact
      exact inductionHypothesis
        (v6_fiber_body_cont_preserves fiberCount state next edge canonical)
        points outputExact

theorem successful_v6_fiber_loop_canonical
    (iter : FiberIter) (fiberCount : Std.Usize)
    (points output : alloc.vec.Vec Point)
    (canonical : PointsCanonical points)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1
      iter fiberCount points = ok (.Ok output)) :
    PointsCanonical output := by
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1
    at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (v6FiberBody fiberCount)
    (iter, points) (.Ok output) run
  exact v6_fiber_trace_canonical fiberCount trace canonical output rfl

theorem successful_selected_v6_points_canonical
    (queries : Array Std.U32 16#usize) (points : alloc.vec.Vec Point)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.selected_circle_fiber_points_shared
      20#u32 (Array.to_slice queries) = ok (.Ok points)) :
    PointsCanonical points := by
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.selected_circle_fiber_points_shared
    at run
  norm_num [V7ProductionCallbacksR29.aspis_core.params.CIRCLE_LOG_ORDER] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨subtracted, subtractedRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨optionResult, optionResultRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨branchResult, branchResultRun, run⟩ := run
  cases branchResult with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Continue exponent =>
      rw [bind_eq_ok_iff] at run
      obtain ⟨upperBound, upperBoundRun, run⟩ := run
      have expectedUpperBoundRun : 31#u32 - 1#u32 = ok (30#u32) := by
        apply checked_sub_eq_wrapping
        norm_num
      have upperBoundExact : upperBound = 30#u32 :=
        Result.ok.inj (upperBoundRun.symm.trans expectedUpperBoundRun)
      rw [upperBoundExact] at run
      norm_num at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨shifted, shiftedRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨shiftResult, shiftResultRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨shiftBranch, shiftBranchRun, run⟩ := run
      cases shiftBranch with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
      | Continue fiberCount =>
          rw [bind_eq_ok_iff] at run
          obtain ⟨iter, iterRun, run⟩ := run
          have initialCanonical : PointsCanonical
              (alloc.vec.Vec.with_capacity Point (Array.to_slice queries).len) := by
            intro point member
            simp [alloc.vec.Vec.with_capacity] at member
          exact successful_v6_fiber_loop_canonical iter fiberCount
            (alloc.vec.Vec.with_capacity Point (Array.to_slice queries).len)
            points initialCanonical run

#print axioms callback_base_point_add_canonical
#print axioms successful_v6_fiber_loop_canonical
#print axioms successful_selected_v6_points_canonical

end V7ProductionCallbacksR30CirclePointCanonical
