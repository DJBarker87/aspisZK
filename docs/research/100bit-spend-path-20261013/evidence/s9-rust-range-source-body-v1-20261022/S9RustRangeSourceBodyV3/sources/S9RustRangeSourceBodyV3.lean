import S9FixedIteratorTransitionsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9RustRangeSourceBodyV3

open AspisR1S9FixedIteratorTransitionsV1
open AspisR1S9FactoredLoopTwoStepV4

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U

/-- The natural-value model of the pinned Rust `Range::next` source body.
The successful branch returns the old start and advances it by one; the
source `Step::forward_unchecked` is only called when `start < end`. -/
def sourceRangeNextValues (start finish : Nat) : Option Nat × (Nat × Nat) :=
  if start < finish then
    (some start, (start + 1, finish))
  else
    (none, (start, finish))

/-- The `TrustedStep` no-overflow condition follows from the reached range
bound: `start < end` and `end` is a valid `usize`. -/
theorem source_forward_one_in_bounds (iter : R)
    (hlt : iter.start.val < iter.end.val) :
    iter.start.val + 1 < 2 ^ UScalarTy.Usize.numBits := by
  have hend := iter.end.hBounds
  omega

/-- The Aeneas `StepUsize` iterator result has exactly the value-level
transition described by the pinned Rust range source body. This is a
source-shaped operational bridge; it does not identify a compiler binary. -/
theorem aeneas_next_matches_source_values (iter : R) :
    ∃ (opt : Option U) (iter' : R),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (opt, iter') ∧
      (opt.map UScalar.val, (iter'.start.val, iter'.end.val)) =
        sourceRangeNextValues iter.start.val iter.end.val := by
  by_cases hlt : iter.start.val < iter.end.val
  · obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter hlt)
    rcases pair with ⟨opt, iter'⟩
    rcases hpost with ⟨hopt, hstart, hend⟩
    refine ⟨opt, iter', hnext, ?_⟩
    simp [sourceRangeNextValues, hlt, hopt, hstart, hend]
  · have hge : iter.end.val ≤ iter.start.val := by omega
    obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) iter hge)
    rcases pair with ⟨opt, iter'⟩
    rcases hpost with ⟨hopt, hiter⟩
    refine ⟨opt, iter', hnext, ?_⟩
    simp [sourceRangeNextValues, hlt, hopt, hiter]

/-- Reachable source-body values for the two-iteration S9 outer range. -/
theorem outer_range_two_source_values :
    sourceRangeNextValues 0 2 = (some 0, (1, 2)) ∧
    sourceRangeNextValues 1 2 = (some 1, (2, 2)) ∧
    sourceRangeNextValues 2 2 = (none, (2, 2)) := by
  norm_num [sourceRangeNextValues]

/-- Reachable source-body values for the four-callback array constructor. -/
theorem callback_range_four_source_values :
    sourceRangeNextValues 0 4 = (some 0, (1, 4)) ∧
    sourceRangeNextValues 1 4 = (some 1, (2, 4)) ∧
    sourceRangeNextValues 2 4 = (some 2, (3, 4)) ∧
    sourceRangeNextValues 3 4 = (some 3, (4, 4)) ∧
    sourceRangeNextValues 4 4 = (none, (4, 4)) := by
  norm_num [sourceRangeNextValues]

/-- The old fixed P6 outer-loop proof supplies the exact iterator results;
this corollary records that those results use the same bounded source-value
transitions at the three outer-loop states. -/
theorem outer_aeneas_results_match_source_values :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start0 =
      .ok (some 0#usize, start1) ∧
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start1 =
      .ok (some 1#usize, start2) ∧
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start2 =
      .ok (none, start2) := by
  exact ⟨AspisR1S9FixedIteratorTransitionsV1.next_start0,
    AspisR1S9FixedIteratorTransitionsV1.next_start1,
    AspisR1S9FixedIteratorTransitionsV1.next_start2⟩

#print axioms source_forward_one_in_bounds
#print axioms aeneas_next_matches_source_values
#print axioms outer_range_two_source_values
#print axioms callback_range_four_source_values
#print axioms outer_aeneas_results_match_source_values

end AspisR1S9RustRangeSourceBodyV3
