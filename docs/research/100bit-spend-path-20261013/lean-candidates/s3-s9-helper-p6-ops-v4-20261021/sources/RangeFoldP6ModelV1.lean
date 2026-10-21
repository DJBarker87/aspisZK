import Aeneas.Std.RangeIter

/-!
Reviewed operational model for the generated `Iterator::fold.default`
operation. It drives the selected Aeneas forward `Range<usize>::next`, threads
callback state, and preserves `Result` failure/divergence. Rust's standard
library correspondence is P6, checked by the paired differential test.
-/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S3S9RangeFoldP6

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U

def rangeNext (r : R) : Result (Option U × R) :=
  core.iter.range.IteratorRange.next core.iter.range.StepUsize r

def rangeNextTrace : Nat → R → Result (List U)
  | 0, _ => .ok []
  | fuel + 1, iter => do
      let (item, iter1) ← rangeNext iter
      match item with
      | none => .ok []
      | some i => do
          let tail ← rangeNextTrace fuel iter1
          .ok (i :: tail)

def foldIndices {S : Type} (step : S → U → Result S) :
    List U → S → Result S
  | [], state => .ok state
  | i :: indices, state => do
      let state1 ← step state i
      foldIndices step indices state1

def rangeFoldRun {S : Type} : Nat → R → (S → U → Result S) → S → Result S
  | 0, _range, _step, state => .ok state
  | fuel + 1, range, step, state => do
      let (item, range') ← rangeNext range
      match item with
      | none => .ok state
      | some i => do
          let state' ← step state i
          rangeFoldRun fuel range' step state'

/-- Successful range traversal determines the exact ordered callback fold. -/
theorem rangeFoldRun_eq_foldIndices_of_trace {S : Type}
    (fuel : Nat) (iter : R) (step : S → U → Result S) (state : S)
    (indices : List U) (htrace : rangeNextTrace fuel iter = .ok indices) :
    rangeFoldRun fuel iter step state = foldIndices step indices state := by
  induction fuel generalizing iter state indices with
  | zero =>
      simp [rangeNextTrace] at htrace
      subst indices
      rfl
  | succ fuel ih =>
      cases hnext : rangeNext iter with
      | fail error => simp [rangeNextTrace, hnext] at htrace
      | div => simp [rangeNextTrace, hnext] at htrace
      | ok pair =>
          rcases pair with ⟨item, iter1⟩
          cases item with
          | none =>
              simp [rangeNextTrace, hnext] at htrace
              subst indices
              simp [rangeFoldRun, hnext, foldIndices]
          | some index =>
              cases htail : rangeNextTrace fuel iter1 with
              | fail error => simp [rangeNextTrace, hnext, htail] at htrace
              | div => simp [rangeNextTrace, hnext, htail] at htrace
              | ok tail =>
                  have hindices : indices = index :: tail := by
                    simpa [rangeNextTrace, hnext, htail] using htrace.symm
                  subst indices
                  cases hs : step state index with
                  | fail error => simp [rangeFoldRun, hnext, hs, foldIndices]
                  | div => simp [rangeFoldRun, hnext, hs, foldIndices]
                  | ok state1 =>
                      have hrec := ih iter1 state1 tail htail
                      simp [rangeFoldRun, hnext, hs, foldIndices, hrec]

#print axioms rangeFoldRun_eq_foldIndices_of_trace
end AspisR1S3S9RangeFoldP6
