import SelectorValueLaneGeneratedSlice
import ExtractedMaskQM31Exact
import ExtractedMaskTowerAdd

/-! A symbolic finite-traversal contract for the generated `IterMut` loop.
The loop is not unrolled. Its deferred writeback function is represented as
the same nested `setAtNat` updates that the source's `next_back` closures
compose. The second theorem obtains each multiplication result and its
canonicality from the checked field operation. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneFiniteTraversal

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev IterMut := core.slice.iter.IterMut QM
abbrev Loop3 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

/-- The deferred writebacks in `add_value_lanes_loop3`, in the order induced
by its nested `next_back` closures. -/
def deferredWrites (values : Nat → QM) (start : Nat) : Nat → IterMut → IterMut
  | 0, im => im
  | n + 1, im =>
      let tail := deferredWrites values (start + 1) n im
      { tail with slice := tail.slice.setAtNat start (values start) }

/-- Generic source-loop execution from pointwise successful multiplication
results. The hypotheses are local operation equations at visited indices;
this theorem derives whole-loop termination and the exact returned iterator
and writeback closure. -/
theorem loop3_finite_of_products
    (iter : IterMut) (back : IterMut → IterMut) (rangeSelector : QM)
    (values : Nat → QM) (n : Nat)
    (hlen : iter.slice.len = iter.i + n)
    (hproducts : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      field.QM31.mul rangeSelector (iter.slice.val[j]) = .ok (values j)) :
    ∃ finalIter finalBack,
      Loop3 iter back rangeSelector = .ok (finalIter, finalBack) ∧
      finalIter.slice = iter.slice ∧
      finalIter.i = iter.i + n ∧
      ∀ im, finalBack im = back (deferredWrites values iter.i n im) := by
  induction n generalizing iter back with
  | zero =>
      have hlenVal : iter.slice.val.length = iter.i := by
        change iter.slice.val.length = iter.i + 0 at hlen
        simpa using hlen
      have hstop : iter.slice.val.length ≤ iter.i := by omega
      have hstop' : ¬ iter.i < iter.slice.val.length := by omega
      refine ⟨iter, back, ?_, rfl, ?_, ?_⟩
      · change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
          iter back rangeSelector = .ok (iter, back)
        rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3.eq_def]
        simp [core.slice.iter.IteratorIterMut.next, hstop']
      · simp
      · intro im
        simp [deferredWrites]
  | succ n ih =>
      have hlenVal : iter.slice.val.length = iter.i + (n + 1) := by
        change iter.slice.val.length = iter.i + (n + 1) at hlen
        exact hlen
      have hhas : iter.i < iter.slice.val.length := by omega
      let residual : QM := iter.slice[iter.i]
      let iter1 : IterMut := { iter with i := iter.i + 1 }
      let nextBack : IterMut → Option QM → IterMut := fun it' x =>
        match x with
        | none => it'
        | some x => { it' with slice := it'.slice.setAtNat iter.i x }
      have hnext :
          core.slice.iter.IteratorIterMut.next iter =
            .ok (some residual, iter1, nextBack) := by
        have hhas' : iter.i < iter.slice.val.length := hhas
        simp [core.slice.iter.IteratorIterMut.next, hhas', residual, iter1, nextBack]
        constructor
        · exact Aeneas.Std.Slice.getElem_Nat_eq iter.slice iter.i hhas
        · funext it' x
          cases x <;> rfl
      have hprod :
          field.QM31.mul rangeSelector residual = .ok (values iter.i) := by
        dsimp [residual]
        exact hproducts iter.i hhas le_rfl
      have hlen1 : iter.slice.len = iter1.i + n := by
        dsimp [iter1]
        omega
      obtain ⟨finalIter, finalBack, hrun, hslice, hindex, hback⟩ :=
        ih iter1 (fun im => back (nextBack im (some (values iter.i))))
          hlen1 (by
            intro j hj hstart
            have hj' : j < iter.slice.val.length := by simpa [iter1] using hj
            have hstart' : iter.i ≤ j := by dsimp [iter1] at hstart; omega
            exact hproducts j hj' hstart')
      refine ⟨finalIter, finalBack, ?_, hslice, ?_, ?_⟩
      · change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
          iter back rangeSelector = .ok (finalIter, finalBack)
        rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3.eq_def]
        simp only [hnext, bind_tc_ok, hprod, bind_tc_ok]
        exact hrun
      · dsimp [iter1] at hindex ⊢
        omega
      · intro im
        rw [hback]
        dsimp [iter1]
        simp [nextBack, deferredWrites]

/-- With a canonical selector and canonical cells in the visited suffix,
the actual generated loop derives every multiply result, output canonicality,
and decoded value, together with finite termination/writeback semantics. -/
theorem loop3_finite_of_canonical_cells
    (iter : IterMut) (back : IterMut → IterMut) (rangeSelector : QM)
    (n : Nat)
    (hlen : iter.slice.len = iter.i + n)
    (hselector : CanonicalQM rangeSelector)
    (hcells : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      CanonicalQM (iter.slice.val[j])) :
    ∃ values : Nat → QM,
      (∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
        CanonicalQM (values j) ∧
        decode (values j) = decode rangeSelector * decode (iter.slice.val[j])) ∧
      ∃ finalIter finalBack,
        Loop3 iter back rangeSelector = .ok (finalIter, finalBack) ∧
        finalIter.slice = iter.slice ∧
        finalIter.i = iter.i + n ∧
        ∀ im, finalBack im = back (deferredWrites values iter.i n im) := by
  classical
  have hlenVal : iter.slice.val.length = iter.i + n := by
    change iter.slice.val.length = iter.i + n at hlen
    exact hlen
  let values : Nat → QM := fun j =>
    if hj : iter.i ≤ j ∧ j < iter.slice.val.length then
      Classical.choose
        (current_qm_mul_exact rangeSelector (iter.slice.val[j]'hj.2
          ) hselector (hcells j hj.2 hj.1))
    else field.QM31.ZERO
  have hvalue : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      CanonicalQM (values j) ∧
      decode (values j) = decode rangeSelector * decode (iter.slice.val[j]) := by
    intro j hj hjlo
    have hspec := Classical.choose_spec
      (current_qm_mul_exact rangeSelector (iter.slice.val[j]'hj
        ) hselector (hcells j hj hjlo))
    have hv : values j = Classical.choose
        (current_qm_mul_exact rangeSelector (iter.slice.val[j]'hj
          ) hselector (hcells j hj hjlo)) := by
      simp [values, hjlo, hj]
    rw [hv]
    exact ⟨hspec.2.1, hspec.2.2⟩
  have hproducts : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      field.QM31.mul rangeSelector (iter.slice.val[j]) = .ok (values j) := by
    intro j hj hjlo
    have hspec := Classical.choose_spec
      (current_qm_mul_exact rangeSelector (iter.slice.val[j]'hj
        ) hselector (hcells j hj hjlo))
    have hv : values j = Classical.choose
        (current_qm_mul_exact rangeSelector (iter.slice.val[j]'hj
          ) hselector (hcells j hj hjlo)) := by
      simp [values, hjlo, hj]
    rw [hv]
    exact hspec.1
  obtain ⟨finalIter, finalBack, hrun, hslice, hindex, hback⟩ :=
    loop3_finite_of_products iter back rangeSelector values n hlen hproducts
  exact ⟨values, hvalue, finalIter, finalBack, hrun, hslice, hindex, hback⟩

/-- The concrete width used by `add_value_lanes`: starting at the beginning
of a 33-cell slice, all 33 multiplications and writebacks are derived from
the canonical selector and canonical input cells. -/
theorem add_value_lanes_loop3_33
    (iter : IterMut) (back : IterMut → IterMut) (rangeSelector : QM)
    (hstart : iter.i = 0) (hlen : iter.slice.len = (33 : Nat))
    (hselector : CanonicalQM rangeSelector)
    (hcells : ∀ j (hj : j < iter.slice.val.length), j < 33 →
      CanonicalQM (iter.slice.val[j])) :
    ∃ values : Nat → QM,
      (∀ j (hj : j < 33),
        CanonicalQM (values j) ∧
        decode (values j) = decode rangeSelector *
          decode (iter.slice.val[j]'(by rw [show iter.slice.val.length = iter.slice.len by rfl, hlen]; exact hj))) ∧
      ∃ finalIter finalBack,
        Loop3 iter back rangeSelector = .ok (finalIter, finalBack) ∧
        finalIter.slice = iter.slice ∧
        finalIter.i = (33 : Nat) ∧
        ∀ im, finalBack im = back (deferredWrites values 0 33 im) := by
  have hlen' : iter.slice.len = iter.i + 33 := by rw [hstart]; simp [hlen]
  have hcells' : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      CanonicalQM (iter.slice.val[j]) := by
    intro j hj hlo
    apply hcells j hj
    rw [show iter.slice.val.length = iter.slice.len by rfl, hlen] at hj
    exact hj
  obtain ⟨values, hvalues, finalIter, finalBack, hrun, hslice, hindex, hback⟩ :=
    loop3_finite_of_canonical_cells iter back rangeSelector 33 hlen' hselector hcells'
  refine ⟨values, ?_, finalIter, finalBack, hrun, hslice, ?_, ?_⟩
  · intro j hj
    have hjval : j < iter.slice.val.length := by
      rw [show iter.slice.val.length = iter.slice.len by rfl, hlen]
      exact hj
    exact hvalues j hjval (by rw [hstart]; omega)
  · rw [hindex, hstart]
  · intro im
    rw [hback, hstart]

#print axioms loop3_finite_of_products
#print axioms loop3_finite_of_canonical_cells
#print axioms add_value_lanes_loop3_33
end AspisR1.SelectorValueLaneFiniteTraversal
