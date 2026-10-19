import TerminalValidateTransitionLoopSource
import ExtractedTerminalEquality
import OccupancyRangeTraversal
import TerminalDigestPublicBranchModel
import Aeneas.Tactic

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev Usize := UScalar UScalarTy.Usize
abbrev Range := core.ops.range.Range Usize
abbrev M31 := field.M31
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Err := AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1

/-- The row operand produced by the exact non-carry branch of the source loop. -/
def expectedWithIter (public1 : Public) (iter1 : Range)
    (level carry : Usize) : Result (Range × Array M31 8#usize) := do
  if level < carry then
    let expected ← AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
    ok (iter1, expected)
  else
    let i ← public1.transition.live_snapshot.next_pair_index >>> level
    let i1 ← lift (i &&& 1#u64)
    let expected ← if i1 = 0#u64 then
      AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
    else
      Array.index_usize public1.transition.live_snapshot.frontier level
    ok (iter1, expected)

private theorem bind_ok {α β : Type} {x : Result α} {f : α → Result β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

private theorem m31_ne_spec (x y : M31) :
    field.M31.Insts.CoreCmpPartialEqM31.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  simp only [core.cmp.PartialEq.ne.default,
    field.M31.Insts.CoreCmpPartialEqM31.eq, bind_tc_ok, WP.spec_ok,
    decide_eq_true_eq]

private def afterNext (public1 : Public) (carry : Usize) (o : Option Usize)
    (iter1 : Range) : Result (core.result.Result Unit Err) :=
  match o with
  | none => .ok (.Ok ())
  | some level =>
    if level = carry then
      if carry < 20#usize then validate_transition_loop public1 iter1 carry
      else do
        let (iter2, expected) ←
          if level < carry then do
            let expected1 ← AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
            ok (iter1, expected1)
          else do
            let i ← public1.transition.live_snapshot.next_pair_index >>> level
            let i1 ← lift (i &&& 1#u64)
            let a ← if i1 = 0#u64 then
              AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
            else Array.index_usize public1.transition.live_snapshot.frontier level
            ok (iter1, a)
        let a ← Array.index_usize public1.transition.candidate_afterstate.next_frontier level
        let b ← core.array.equality.PartialEqArray.ne
          field.M31.Insts.CoreCmpPartialEqM31 a expected
        if b = true then
          ok (.Err AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
        else validate_transition_loop public1 iter2 carry
    else do
      let (iter2, expected) ←
        if level < carry then do
          let expected1 ← AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
          ok (iter1, expected1)
        else do
          let i ← public1.transition.live_snapshot.next_pair_index >>> level
          let i1 ← lift (i &&& 1#u64)
          let a ← if i1 = 0#u64 then
            AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
          else Array.index_usize public1.transition.live_snapshot.frontier level
          ok (iter1, a)
      let a ← Array.index_usize public1.transition.candidate_afterstate.next_frontier level
      let b ← core.array.equality.PartialEqArray.ne
        field.M31.Insts.CoreCmpPartialEqM31 a expected
      if b = true then
        ok (.Err AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
      else validate_transition_loop public1 iter2 carry

private def afterNextResult (public1 : Public) (carry : Usize)
    (r : Result (Option Usize × Range)) : Result (core.result.Result Unit Err) := do
  let (o, iter1) ← r
  afterNext public1 carry o iter1

private def afterNextPair (public1 : Public) (carry : Usize)
    (pair : Option Usize × Range) : Result (core.result.Result Unit Err) :=
  afterNext public1 carry pair.1 pair.2

private theorem afterNextResult_bind (public1 : Public) (carry : Usize)
    (r : Result (Option Usize × Range)) :
    afterNextResult public1 carry r = r >>= afterNextPair public1 carry := by
  cases r with
  | ok pair => cases pair with | mk o it => rfl
  | fail e => rfl
  | div => rfl

/-- A successful exact source iteration at a non-carry row returns the next
iterator and the precise expected-array read, proves the candidate frontier
row equals it, and leaves a successful recursive suffix. -/
theorem noncarry_step_success
    (public1 : Public) (iter : Range) (carry : Usize)
    (hlt : iter.start.val < iter.end.val)
    (hne : iter.start ≠ carry)
    (hsuccess : validate_transition_loop public1 iter carry = .ok (.Ok ())) :
    ∃ iter1 expected,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter1) ∧
      expectedWithIter public1 iter1 iter.start carry = .ok (iter1, expected) ∧
      Array.index_usize public1.transition.candidate_afterstate.next_frontier
        iter.start = .ok expected ∧
      validate_transition_loop public1 iter1 carry = .ok (.Ok ()) := by
  obtain ⟨iter1, hnext, _, _, _⟩ :=
    AspisR1.OccupancyRangeTraversal.next_step iter hlt
  rw [validate_transition_loop.eq_def] at hsuccess
  change afterNextResult public1 carry
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) =
    .ok (.Ok ()) at hsuccess
  rw [afterNextResult_bind] at hsuccess
  have hcontinuation := congrArg
    (fun result => result >>= afterNextPair public1 carry) hnext
  have hsuccess' : afterNext public1 carry (some iter.start) iter1 = .ok (.Ok ()) := by
    have hsuccessPair : .ok (some iter.start, iter1) >>= afterNextPair public1 carry =
        .ok (.Ok ()) := hcontinuation.symm.trans hsuccess
    exact hsuccessPair
  have hne' : ¬ iter.start = carry := by
    intro h
    exact hne h
  simp only [afterNext, if_neg hne'] at hsuccess'
  rcases bind_ok hsuccess' with ⟨pair, hpair, hrest⟩
  cases pair with
  | mk iter2 expected =>
    have hpair' : expectedWithIter public1 iter1 iter.start carry = .ok (iter2, expected) := by
      change expectedWithIter public1 iter1 iter.start carry = .ok (iter2, expected)
      exact hpair
    have hiter2 : iter2 = iter1 := by
      have hpairResult : expectedWithIter public1 iter1 iter.start carry =
          .ok (iter2, expected) := hpair'
      unfold expectedWithIter at hpairResult
      split at hpairResult
      · rcases bind_ok hpairResult with ⟨expected0, _, hpairResult⟩
        have := congrArg Prod.fst (Result.ok.inj hpairResult)
        exact this.symm
      · rcases bind_ok hpairResult with ⟨shift, _, hpairResult⟩
        rcases bind_ok hpairResult with ⟨bit, _, hpairResult⟩
        split at hpairResult
        · rcases bind_ok hpairResult with ⟨expected0, _, hpairResult⟩
          have := congrArg Prod.fst (Result.ok.inj hpairResult)
          exact this.symm
        · rcases bind_ok hpairResult with ⟨expected0, _, hpairResult⟩
          have := congrArg Prod.fst (Result.ok.inj hpairResult)
          exact this.symm
    subst iter2
    rcases bind_ok hrest with ⟨actual, hread, hrest⟩
    rcases bind_ok hrest with ⟨different, hcmp, hrest⟩
    cases different with
    | true => simp at hrest
    | false =>
      have heq : actual = expected := by
        classical
        have hdec : decide (actual ≠ expected) = false := by
          have hspec := AspisR1TerminalValidator.TerminalEquality.array_ne_value
            field.M31.Insts.CoreCmpPartialEqM31 m31_ne_spec actual expected
          rw [hcmp] at hspec
          simpa using hspec
        exact not_ne_iff.mp (of_decide_eq_false hdec)
      have hloop : validate_transition_loop public1 iter1 carry = .ok (.Ok ()) := by
        simpa using hrest
      refine ⟨iter1, expected, hnext, ?_, ?_, hloop⟩
      · exact hpair'
      · rw [hread, heq]

#print axioms noncarry_step_success

/-- A carry row below level 20 is skipped exactly as in the source and leaves
a successful recursive suffix. -/
theorem carry_step_success
    (public1 : Public) (iter : Range) (carry : Usize)
    (hlt : iter.start.val < iter.end.val)
    (hcarry : iter.start = carry) (hcarryLt : carry < 20#usize)
    (hsuccess : validate_transition_loop public1 iter carry = .ok (.Ok ())) :
    ∃ iter1,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter1) ∧
      validate_transition_loop public1 iter1 carry = .ok (.Ok ()) := by
  obtain ⟨iter1, hnext, _, _, _⟩ :=
    AspisR1.OccupancyRangeTraversal.next_step iter hlt
  rw [validate_transition_loop.eq_def] at hsuccess
  change afterNextResult public1 carry
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) =
    .ok (.Ok ()) at hsuccess
  rw [afterNextResult_bind] at hsuccess
  have hcontinuation := congrArg
    (fun result => result >>= afterNextPair public1 carry) hnext
  have hsuccess' : afterNext public1 carry (some iter.start) iter1 = .ok (.Ok ()) := by
    have hsuccessPair : .ok (some iter.start, iter1) >>= afterNextPair public1 carry =
        .ok (.Ok ()) := hcontinuation.symm.trans hsuccess
    exact hsuccessPair
  simp only [afterNext, if_pos hcarry, if_pos hcarryLt] at hsuccess'
  exact ⟨iter1, hnext, hsuccess'⟩

#print axioms carry_step_success
end AspisR1TerminalValidateTransitionCandidate
