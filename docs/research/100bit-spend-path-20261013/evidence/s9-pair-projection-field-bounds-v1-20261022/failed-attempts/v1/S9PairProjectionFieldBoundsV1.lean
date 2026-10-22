import S9PairCallerStepOwnedFieldBridgeV1
import S9OwnedFieldBoundedIndexV2

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairProjectionFieldBoundsV1
open AspisR1S9PairCallerStepV1

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : Std.Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length := (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

/-- A successfully continued actual projection body reads a bounded field.
The bound follows from its same-execution four-cell libra read; it is not
assumed from an iterator invariant. The field value is canonical and its
actual owned reader agrees with the checked reader at that same index. -/
theorem continued_projection_field_is_bounded_canonical
    (f : Slice U8) (libra : Array field.WideExact 4#usize)
    (iter iterOut : core.ops.range.Range Usize)
    (parts partsOut : Array field.WideExact 7#usize)
    (hbody : weights.Weights.pair_s2_libra_parts_projection_loop.body
      f libra iter parts = .ok (.cont (iterOut, partsOut))) :
    ∃ (j : Usize) (value : field.WideExact)
      (owned : AspisR1S9FieldOwnedV1.field.wide_exact.WideExact),
      weights.field f j = .ok value ∧
      j.val < 4 ∧
      AspisR1S9FieldOwnedV1.weights.field f j = .ok owned ∧
      value = fromOwnedW owned ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (toP6W value) ∧
      AspisR1WeightsFieldCurrent.weights.field
        AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes f j =
        .ok owned := by
  unfold weights.Weights.pair_s2_libra_parts_projection_loop.body at hbody
  cases hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp only [hnext, bind_tc_fail] at hbody; cases hbody
  | div => simp only [hnext, bind_tc_div] at hbody; cases hbody
  | ok p =>
      rcases p with ⟨opt, iter1⟩
      cases opt with
      | none => simp only [hnext, bind_tc_ok] at hbody; cases hbody
      | some j =>
          simp only [hnext, bind_tc_ok] at hbody
          obtain ⟨old, hold, hrest⟩ := bind_success _ _ _ hbody
          obtain ⟨value, hfield, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨coef, hcoef, hrest⟩ := bind_success _ _ _ hrest
          have hj : j.val < 4 := by
            simpa using index_success_bound libra j coef hcoef
          obtain ⟨owned, start, next, finish, selected, arr, howned, hmap,
            hstart, hnext1, hfinish, hselected, hlen, hslice, hlimbs,
            hparser, hpacked, hcanonical⟩ :=
            AspisR1S9PairCallerStepOwnedFieldBridgeV1.pair_field_success_actual_reader
              f j value hfield
          have hchecked := howned
          rw [AspisR1S9OwnedFieldBoundedIndexV1.owned_reader_eq_checked_reader
            f j (by omega)] at hchecked
          exact ⟨j, value, owned, hfield, hj, howned, hmap, hcanonical, hchecked⟩

#print axioms continued_projection_field_is_bounded_canonical
end AspisR1S9PairProjectionFieldBoundsV1
