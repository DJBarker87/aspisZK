import V7CallerCurrentReleaseR30SemanticPointCanonical
import V7CallerCurrentReleaseR26GroupedAllSame

/-!
# Canonicality of the three statement points

The generated statement-point helper keeps the semantic point, constructs its
successor with a reverse carry loop, and flips coordinates six and seven for
the third point.  This module proves all three arrays canonical from a
canonical semantic point by following both generated loop traces.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30StatementPointsCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR30SemanticPointCanonical

abbrev RawQM31 := field.QM31
abbrev Point := Array RawQM31 10#usize
abbrev Points := Array Point 3#usize

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩
local instance : Inhabited Point :=
  ⟨Array.repeat 10#usize field.QM31.ZERO⟩

def CanonicalPoints (points : Points) : Prop :=
  ∀ row coordinate, row < 3 → coordinate < 10 →
    GeneratedCanonicalQM31 points.val[row]!.val[coordinate]!

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem one_canonical :
    GeneratedCanonicalQM31 field.QM31.ONE := by
  exact V7CallerCurrentReleaseR26GroupedAllSame.oneCanonical

private theorem canonical_of_mul
    (left right out : RawQM31)
    (leftCanonical : GeneratedCanonicalQM31 left)
    (rightCanonical : GeneratedCanonicalQM31 right)
    (run : field.QM31.mul left right = ok out) :
    GeneratedCanonicalQM31 out := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_qm31_mul_corresponds left right leftCanonical rightCanonical
  have exact : out = expected := Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

private theorem canonical_of_add
    (left right out : RawQM31)
    (leftCanonical : GeneratedCanonicalQM31 left)
    (rightCanonical : GeneratedCanonicalQM31 right)
    (run : field.QM31.add left right = ok out) :
    GeneratedCanonicalQM31 out := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_qm31_add_corresponds left right leftCanonical rightCanonical
  have exact : out = expected := Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

private theorem canonical_of_sub
    (left right out : RawQM31)
    (leftCanonical : GeneratedCanonicalQM31 left)
    (rightCanonical : GeneratedCanonicalQM31 right)
    (run : field.QM31.sub left right = ok out) :
    GeneratedCanonicalQM31 out := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_qm31_sub_corresponds left right leftCanonical rightCanonical
  have exact : out = expected := Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

private theorem canonical_index
    (point : Point) (index : Std.Usize) (value : RawQM31)
    (canonical : CanonicalPoint point)
    (run : Array.index_usize point index = ok value) :
    GeneratedCanonicalQM31 value := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i present
    have presentList : point.val[index.val]? = some value := by
      simpa [Result.ok.inj run] using present
    have bound : index.val < point.val.length := by
      by_contra outOfBounds
      have absent : point.val[index.val]? = none :=
        List.getElem?_eq_none (by omega)
      rw [absent] at presentList
      cases presentList
    have exact : value = point.val[index.val]! := by
      symm
      exact List.getElem!_of_getElem? presentList
    rw [exact]
    exact canonical index.val (by simpa [Array.length_eq] using bound)

private theorem canonical_update
    (point next : Point) (index : Std.Usize) (value : RawQM31)
    (canonical : CanonicalPoint point)
    (valueCanonical : GeneratedCanonicalQM31 value)
    (run : Array.update point index value = ok next) :
    CanonicalPoint next := by
  have facts : index.val < 10 ∧ next = point.set index value := by
    unfold Array.update at run
    split at run
    · cases run
    · rename_i present
      have presentSome : (point.val[index.val]?).isSome := by
        simpa using congrArg Option.isSome present
      have bound : index.val < point.val.length := by
        by_contra outOfBounds
        have absent : point.val[index.val]? = none :=
          List.getElem?_eq_none (by omega)
        rw [absent] at presentSome
        cases presentSome
      exact ⟨by simpa [Array.length_eq] using bound,
        (Result.ok.inj run).symm⟩
  rw [facts.2]
  unfold CanonicalPoint
  intro target targetBound
  by_cases same : target = index.val
  · subst target
    rw [Array.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ ⟨by
      simpa [Array.length_eq] using facts.1, rfl⟩]
    exact valueCanonical
  · rw [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
    exact canonical target targetBound

abbrev SuccessorIter :=
  core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)
abbrev SuccessorState := SuccessorIter × Point × RawQM31

def successorBody (z : Point) (state : SuccessorState) :
    Result (ControlFlow SuccessorState Point) :=
  v6_transcript.v6_statement_points_loop0.body z state.1 state.2.1
    state.2.2

private theorem continuing_successor_preserves
    (z : Point) (zCanonical : CanonicalPoint z)
    (state next : SuccessorState)
    (edge : successorBody z state = ok (cont next))
    (successorCanonical : CanonicalPoint state.2.1)
    (carryCanonical : GeneratedCanonicalQM31 state.2.2) :
    CanonicalPoint next.2.1 ∧ GeneratedCanonicalQM31 next.2.2 := by
  rcases state with ⟨iter, successor, carry⟩
  rcases next with ⟨iterNext, successorNext, carryNext⟩
  unfold successorBody at edge
  unfold v6_transcript.v6_statement_points_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some coordinate =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨bit, bitRun, edge⟩ := edge
      have bitCanonical := canonical_index z coordinate bit zCanonical bitRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨bitCarry, bitCarryRun, edge⟩ := edge
      have bitCarryCanonical := canonical_of_mul bit carry bitCarry
        bitCanonical carryCanonical bitCarryRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨bitPlusCarry, bitPlusCarryRun, edge⟩ := edge
      have bitPlusCarryCanonical := canonical_of_add bit carry bitPlusCarry
        bitCanonical carryCanonical bitPlusCarryRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨twiceBitCarry, twiceRun, edge⟩ := edge
      have twiceCanonical := canonical_of_add bitCarry bitCarry
        twiceBitCarry bitCarryCanonical bitCarryCanonical twiceRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨coordinateOut, subRun, edge⟩ := edge
      have coordinateCanonical := canonical_of_sub bitPlusCarry twiceBitCarry
        coordinateOut bitPlusCarryCanonical twiceCanonical subRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨successorAfter, updateRun, edge⟩ := edge
      have outputExact := ControlFlow.cont.inj (Result.ok.inj edge)
      simp only [Prod.mk.injEq] at outputExact
      rcases outputExact with ⟨iterExact, successorExact, carryExact⟩
      subst successorNext
      subst carryNext
      exact ⟨canonical_update successor successorAfter coordinate coordinateOut
        successorCanonical coordinateCanonical updateRun,
        bitCarryCanonical⟩

private theorem done_successor_canonical
    (z : Point) (state : SuccessorState) (output : Point)
    (edge : successorBody z state = ok (done output))
    (canonical : CanonicalPoint state.2.1) :
    CanonicalPoint output := by
  rcases state with ⟨iter, successor, carry⟩
  unfold successorBody at edge
  unfold v6_transcript.v6_statement_points_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      have exact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← exact]
      exact canonical
  | some coordinate =>
      repeat' first
        | rw [bind_eq_ok_iff] at edge
          obtain ⟨_, _, edge⟩ := edge
      cases edge

private theorem successor_trace_canonical
    (z : Point) (zCanonical : CanonicalPoint z)
    {state : SuccessorState} {output : Point}
    (trace : ExactLoopTrace (successorBody z) state output)
    (successorCanonical : CanonicalPoint state.2.1)
    (carryCanonical : GeneratedCanonicalQM31 state.2.2) :
    CanonicalPoint output := by
  induction trace with
  | done edge => exact done_successor_canonical z _ _ edge successorCanonical
  | @cont _ next _ edge tail inductionHypothesis =>
      have nextCanonical := continuing_successor_preserves z zCanonical
        _ next edge successorCanonical carryCanonical
      exact inductionHypothesis nextCanonical.1 nextCanonical.2

theorem successful_statement_successor_loop_canonical
    (iter : SuccessorIter) (z successor output : Point)
    (carry : RawQM31) (zCanonical : CanonicalPoint z)
    (successorCanonical : CanonicalPoint successor)
    (carryCanonical : GeneratedCanonicalQM31 carry)
    (run : v6_transcript.v6_statement_points_loop0 iter z successor carry =
      ok output) :
    CanonicalPoint output := by
  unfold v6_transcript.v6_statement_points_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (successorBody z)
    (iter, successor, carry) output run
  exact successor_trace_canonical z zCanonical trace successorCanonical
    carryCanonical

abbrev XorIter := core.array.iter.IntoIter Std.Usize 2#usize
abbrev XorState := XorIter × Point

def xorBody (state : XorState) : Result (ControlFlow XorState Point) :=
  v6_transcript.v6_statement_points_loop1.body state.1 state.2

private theorem continuing_xor_preserves
    (state next : XorState)
    (edge : xorBody state = ok (cont next))
    (canonical : CanonicalPoint state.2) :
    CanonicalPoint next.2 := by
  rcases state with ⟨iter, point⟩
  rcases next with ⟨iterNext, pointNext⟩
  unfold xorBody at edge
  unfold v6_transcript.v6_statement_points_loop1.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some coordinate =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨value, valueRun, edge⟩ := edge
      have valueCanonical := canonical_index point coordinate value canonical
        valueRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flipped, subRun, edge⟩ := edge
      have flippedCanonical := canonical_of_sub field.QM31.ONE value flipped
        one_canonical valueCanonical subRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨pointAfter, updateRun, edge⟩ := edge
      have outputExact := ControlFlow.cont.inj (Result.ok.inj edge)
      simp only [Prod.mk.injEq] at outputExact
      rw [← outputExact.2]
      exact canonical_update point pointAfter coordinate flipped canonical
        flippedCanonical updateRun

private theorem done_xor_canonical
    (state : XorState) (output : Point)
    (edge : xorBody state = ok (done output))
    (canonical : CanonicalPoint state.2) :
    CanonicalPoint output := by
  rcases state with ⟨iter, point⟩
  unfold xorBody at edge
  unfold v6_transcript.v6_statement_points_loop1.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      have exact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← exact]
      exact canonical
  | some coordinate =>
      repeat' first
        | rw [bind_eq_ok_iff] at edge
          obtain ⟨_, _, edge⟩ := edge
      cases edge

private theorem xor_trace_canonical
    {state : XorState} {output : Point}
    (trace : ExactLoopTrace xorBody state output)
    (canonical : CanonicalPoint state.2) :
    CanonicalPoint output := by
  induction trace with
  | done edge => exact done_xor_canonical _ _ edge canonical
  | @cont _ next _ edge tail inductionHypothesis =>
      exact inductionHypothesis
        (continuing_xor_preserves _ next edge canonical)

theorem successful_statement_xor_loop_canonical
    (iter : XorIter) (point output : Point)
    (canonical : CanonicalPoint point)
    (run : v6_transcript.v6_statement_points_loop1 iter point = ok output) :
    CanonicalPoint output := by
  unfold v6_transcript.v6_statement_points_loop1 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace xorBody (iter, point)
    output run
  exact xor_trace_canonical trace canonical

private theorem array_make_three_canonical
    (point0 point1 point2 : Point)
    (canonical0 : CanonicalPoint point0)
    (canonical1 : CanonicalPoint point1)
    (canonical2 : CanonicalPoint point2) :
    CanonicalPoints (Array.make 3#usize [point0, point1, point2]) := by
  intro row coordinate rowBound coordinateBound
  have rowCases : row = 0 ∨ row = 1 ∨ row = 2 := by omega
  rcases rowCases with rowZero | rowRest
  · subst row
    simpa [Array.make] using canonical0 coordinate coordinateBound
  · rcases rowRest with rowOne | rowTwo
    · subst row
      simpa [Array.make] using canonical1 coordinate coordinateBound
    · subst row
      simpa [Array.make] using canonical2 coordinate coordinateBound

/-- A canonical statement-point entry through proof-carrying indexing.

Keeping this form public lets downstream source bridges avoid coupling to the
default-value instances used by generated array indexing. -/
theorem canonical_points_entry
    (points : Points) (canonical : CanonicalPoints points)
    (row coordinate : Nat) (rowBound : row < points.val.length)
    (coordinateBound : coordinate < (points.val[row]'rowBound).val.length) :
    GeneratedCanonicalQM31
      ((points.val[row]'rowBound).val[coordinate]'coordinateBound) := by
  have rowBoundThree : row < 3 := by
    simpa [Array.length_eq] using rowBound
  have coordinateBoundTen : coordinate < 10 := by
    simpa [Array.length_eq] using coordinateBound
  have source := canonical row coordinate rowBoundThree coordinateBoundTen
  rw [getElem!_pos points.val row rowBound] at source
  rw [getElem!_pos (points.val[row]'rowBound).val coordinate coordinateBound]
    at source
  exact source

theorem successful_v6_statement_points_canonical
    (z : Point) (points : Points)
    (canonical : CanonicalPoint z)
    (run : v6_transcript.v6_statement_points z = ok points) :
    CanonicalPoints points := by
  unfold v6_transcript.v6_statement_points at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨slice, sliceRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨last, lastRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨lastValue, lastValueRun, run⟩ := run
  have lastCanonical := canonical_index z last lastValue canonical lastValueRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨lastComplement, complementRun, run⟩ := run
  have complementCanonical := canonical_of_sub field.QM31.ONE lastValue
    lastComplement one_canonical lastCanonical complementRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨predecessor, predecessorRun, run⟩ := run
  have predecessorCanonical := canonical_update z predecessor last
    lastComplement canonical complementCanonical predecessorRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨successorIter, successorIterRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨successor, successorRun, run⟩ := run
  have successorCanonical := successful_statement_successor_loop_canonical
    successorIter z predecessor successor lastValue canonical
    predecessorCanonical lastCanonical successorRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨xorIter, xorIterRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨xorPoint, xorRun, run⟩ := run
  have xorCanonical := successful_statement_xor_loop_canonical xorIter z
    xorPoint canonical xorRun
  have outputExact := Result.ok.inj run
  rw [← outputExact]
  exact array_make_three_canonical z successor xorPoint canonical
    successorCanonical xorCanonical

#print axioms successful_statement_successor_loop_canonical
#print axioms successful_statement_xor_loop_canonical
#print axioms successful_v6_statement_points_canonical

end V7CallerCurrentReleaseR30StatementPointsCanonical
