import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.RevFoldRefinementV2

abbrev ActualRevRange :=
  core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

def actualRevNext (iter : ActualRevRange) :
    Result (Option Usize × ActualRevRange) :=
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
    iter

def actualInitialRevRange : ActualRevRange :=
  ⟨{ start := 0#usize, «end» := 7#usize }⟩

def actualRevNextTrace : Nat → ActualRevRange → Option (List Nat)
  | 0, _ => some []
  | n + 1, iter =>
      match actualRevNext iter with
      | .ok (none, _) => some []
      | .ok (some index, iter1) => do
          let rest ← actualRevNextTrace n iter1
          some (index.val :: rest)
      | .fail _ => none
      | .div => none

theorem actual_rev_next_trace_zero_seven :
    actualRevNextTrace 8 actualInitialRevRange =
      some [6, 5, 4, 3, 2, 1, 0] := by
  decide

def foldIndices {α : Type} (step : α → Nat → Result α) :
    List Nat → α → Result α
  | [], state => .ok state
  | index :: indices, state => do
      let state1 ← step state index
      foldIndices step indices state1

def actualRfoldLoop {α : Type} : Nat → ActualRevRange →
    (α → Nat → Result α) → α → Result α
  | 0, _, _, state => .ok state
  | n + 1, iter, step, state => do
      let (item, iter1) ← actualRevNext iter
      match item with
      | none => .ok state
      | some index => do
          let state1 ← step state index.val
          actualRfoldLoop n iter1 step state1

theorem actualRfoldLoop_eq_foldIndices {α : Type} (fuel : Nat)
    (iter : ActualRevRange) (step : α → Nat → Result α) (state : α)
    (indices : List Nat)
    (htrace : actualRevNextTrace fuel iter = some indices) :
    actualRfoldLoop fuel iter step state = foldIndices step indices state := by
  induction fuel generalizing iter state indices with
  | zero =>
      simp [actualRevNextTrace] at htrace
      subst indices
      rfl
  | succ fuel ih =>
      cases hnext : actualRevNext iter with
      | fail error =>
          simp [actualRevNextTrace, hnext] at htrace
      | div =>
          simp [actualRevNextTrace, hnext] at htrace
      | ok pair =>
          rcases pair with ⟨item, iter1⟩
          cases item with
          | none =>
              simp [actualRevNextTrace, hnext] at htrace
              subst indices
              simp [actualRfoldLoop, hnext, foldIndices]
          | some index =>
              cases htail : actualRevNextTrace fuel iter1 with
              | none =>
                  simp [actualRevNextTrace, hnext, htail] at htrace
              | some tail =>
                  have hindices : indices = index.val :: tail := by
                    simpa [actualRevNextTrace, hnext, htail] using htrace.symm
                  subst indices
                  cases hs : step state index.val with
                  | ok state1 =>
                      have hrec := ih iter1 state1 tail htail
                      simp [actualRfoldLoop, hnext, hs, foldIndices, hrec]
                  | fail error =>
                      simp [actualRfoldLoop, hnext, hs, foldIndices]
                  | div =>
                      simp [actualRfoldLoop, hnext, hs, foldIndices]

theorem actual_rfold_loop_zero_seven {α : Type}
    (step : α → Nat → Result α) (state : α) :
    actualRfoldLoop 8 actualInitialRevRange step state =
      foldIndices step [6, 5, 4, 3, 2, 1, 0] state := by
  rw [actualRfoldLoop_eq_foldIndices 8 actualInitialRevRange step state
    [6, 5, 4, 3, 2, 1, 0] actual_rev_next_trace_zero_seven]

#print axioms actual_rev_next_trace_zero_seven
#print axioms actualRfoldLoop_eq_foldIndices
#print axioms actual_rfold_loop_zero_seven

end AspisR1CurrentWide.RevFoldRefinementV2
