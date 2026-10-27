import FIx_ConservationMeaning
set_option autoImplicit false
namespace AspisR1.FIy_IteratorTraversal
open Aeneas Aeneas.Std Result FIq_Native
abbrev QM := field.QM31
abbrev IterMut := core.slice.iter.IterMut QM
abbrev Loop3 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
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
theorem products
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
        simp only [hnext, bind_tc_ok]
        dsimp
        rw [hprod]
        simp only [bind_tc_ok]
        exact hrun
      · dsimp [iter1] at hindex ⊢
        omega
      · intro im
        rw [hback]
        dsimp [iter1]
        simp [nextBack, deferredWrites]


#print axioms products
end AspisR1.FIy_IteratorTraversal
