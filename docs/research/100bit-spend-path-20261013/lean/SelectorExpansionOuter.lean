import SelectorExpansionCorrectness
import ExtractedMaskPreparedState
import ExtractedMaskReducerOps
import ExtractedMaskConstants

/-! Forward slice traversal for the generated selected-selector expansion.
The pointwise model is a symbolic list fold; no finite expansion is unfolded. -/
set_option autoImplicit false
namespace AspisR1.SelectorExpansionOuter

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
open AspisR1.SelectorExpansionCorrectness
open AspisR1.ExtractedMaskPreparedState
open AspisR1.ExtractedMaskReverseRange
open AspisR1.ExtractedMaskConstants

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def expandListModel : List QM → Nat → (Nat → ExactQM) → Nat → ExactQM
  | [], _, w, j => w j
  | x :: xs, level, w, j =>
      expandListModel xs (level + 1)
        (selectorDescending (decode x) (2 ^ level) w) j

private theorem list_drop_split {α : Type} (ys : List α) (i : Nat)
    (hi : i < ys.length) : ys.drop i = ys[i] :: ys.drop (i+1) := by
  induction ys generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < ys.length := by simpa using hi
          simpa using ih i hi'

private theorem slice_next_step (iter : core.slice.iter.Iter QM) (x : QM)
    (xs : List QM) (hdrop : iter.slice.val.drop iter.i = x :: xs) :
    core.slice.iter.IteratorSliceIter.next iter =
      .ok (some x, {iter with i := iter.i + 1}) := by
  have hstep : iter.i < iter.slice.val.length := by
    have hlen := congrArg List.length hdrop
    rw [List.length_drop] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have hvalue : iter.slice.val[iter.i] = x := by
    have hsplit := list_drop_split iter.slice.val iter.i hstep
    rw [hdrop] at hsplit
    have hh := congrArg List.head? hsplit
    change some x = some (iter.slice.val[iter.i]) at hh
    exact (Option.some.inj hh).symm
  calc
    core.slice.iter.IteratorSliceIter.next iter =
        .ok (some iter.slice.val[iter.i], {iter with i := iter.i + 1}) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, hstep,
        ↓reduceDIte]
      rfl
    _ = .ok (some x, {iter with i := iter.i + 1}) := by rw [hvalue]

private theorem slice_drop_step (iter : core.slice.iter.Iter QM) (x : QM)
    (xs : List QM) (hdrop : iter.slice.val.drop iter.i = x :: xs) :
    iter.slice.val.drop (iter.i + 1) = xs := by
  have hstep : iter.i < iter.slice.val.length := by
    have hlen := congrArg List.length hdrop
    rw [List.length_drop] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have hsplit := list_drop_split iter.slice.val iter.i hstep
  rw [hdrop] at hsplit
  have ht := congrArg List.tail hsplit
  simpa using ht.symm

private theorem selectorWrite_outside (x : ExactQM) (i : Nat)
    (w : Nat → ExactQM) (j : Nat) (hj : 2*i+1 < j) :
    selectorWrite x i w j = w j := by
  unfold selectorWrite
  simp [Function.update, show j ≠ 2*i+1 by omega,
    show j ≠ 2*i by omega]

private theorem selectorDescending_outside (x : ExactQM) :
    ∀ n (w : Nat → ExactQM) (j N : Nat),
      2*n ≤ N → N ≤ j → selectorDescending x n w j = w j
  | 0, w, j, N, _, _ => rfl
  | n+1, w, j, N, hcap, hj => by
      have hstep : 2*n+1 < j := by omega
      simp only [selectorDescending]
      rw [selectorDescending_outside x n (selectorWrite x n w) j N (by omega) hj]
      exact selectorWrite_outside x n w j hstep

private theorem usize_double (len : Usize) (k : Nat)
    (hlen : len.val = 2 ^ k) (hbound : len.val * 2 < UScalar.size .Usize) :
    ∃ len1 : Usize, (len * 2#usize : Result Usize) = .ok len1 ∧ len1.val = 2 ^ (k+1) := by
  obtain ⟨len1, hmul, hval⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := len) (y := 2#usize) (by
      have hmaxplus : Usize.max + 1 = UScalar.size UScalarTy.Usize := by
          rw [UScalar.size_UScalarTyUsize]
          exact Usize.size_scalarTac_eq.1.symm
      have hlt : len.val * 2 < Nat.succ Usize.max := by
        simpa [Nat.succ_eq_add_one, ← hmaxplus] using hbound
      exact Nat.lt_succ_iff.mp hlt))
  refine ⟨len1, hmul, ?_⟩
  have hv : len1.val = len.val * 2 := by simpa using hval
  rw [hv, hlen, pow_succ]

private theorem range_rev_ok (len : Usize) :
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ({ start := 0#usize, «end» := len } : core.ops.range.Range Usize) =
        .ok (⟨{ start := 0#usize, «end» := len }⟩ :
          AspisR1.ExtractedMaskReverseRange.ReverseRange) := rfl

private theorem array_update_success {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (x : α) (hi : i.val < N.val) :
    ∃ out : Array α N, Array.update a i x = .ok out ∧ out = a.set i x := by
  obtain ⟨out, hrun, hset⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  exact ⟨out, hrun, hset⟩

private theorem set_canonical {N : Usize} (a : Array QM N) (i : Usize) (x : QM)
    (ha : canonicalArray a) (hx : Canonical x) (hi : i.val < N.val) :
    canonicalArray (a.set i x) := by
  intro j
  have hj : j.val < a.val.length := by simpa [a.property] using j.isLt
  have hjSet : j.val < (a.val.set i.val x).length := by simpa using hj
  change Canonical ((a.val.set i.val x)[j.val]'hjSet)
  by_cases heq : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjSet)
      simpa [heq] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = a.val[j.val]'hj := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        heq hjSet)
    rw [hcell]
    exact ha j

private theorem decodedArray_set_outer {N : Usize} (a : Array QM N) (i : Usize)
    (x : QM) (hi : i.val < N.val) :
    decodedArray (a.set i x) = Function.update (decodedArray a) i.val (decode x) := by
  funext j
  by_cases hj : j < N.val
  · by_cases heq : i.val = j
    · subst j
      have hjSet : i.val < (a.val.set i.val x).length := by simpa using hi
      have hcell : (a.val.set i.val x)[i.val]'hjSet = x := by
        exact List.getElem_set_self (l := a.val) (i := i.val) (a := x)
          (by simpa using hi)
      simp only [decodedArray, decodedAt, Array.set_val_eq, dif_pos hj]
      rw [hcell]
      simp [Function.update]
    · have hjSet : j < (a.val.set i.val x).length := by simpa using hj
      have hcell : (a.val.set i.val x)[j]'hjSet = a.val[j]'(by simpa [a.property] using hj) := by
        exact List.getElem_set_ne (l := a.val) (i := i.val) (j := j) heq
          (by simpa [a.property] using hjSet)
      simp only [decodedArray, decodedAt, Array.set_val_eq, dif_pos hj]
      rw [hcell]
      have hji : j ≠ i.val := by omega
      simp [decodedAt, hj, Function.update, hji]
  · have hji : j ≠ i.val := by omega
    simp [decodedArray, decodedAt, Array.set_val_eq, hj, Function.update, hji]

/-- The generated outer loop processes each slice element once and runs the
actual reverse expansion loop at the current power-of-two width. -/
theorem expand_loop_model
    {N : Usize} (iter : core.slice.iter.Iter QM) (weights : Array QM N)
    (len : Usize) (level : Nat) (xs : List QM)
    (hdrop : iter.slice.val.drop iter.i = xs)
    (hlen : len.val = 2 ^ level)
    (hcapacity : 2 ^ (level + xs.length) ≤ N.val)
    (hweights : canonicalArray weights)
    (hcoords : ∀ x ∈ xs, Canonical x) :
    ∃ out : Array QM N,
      pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 iter weights len =
        .ok out ∧ canonicalArray out ∧
      ∀ j : Fin N.val,
        decodedArray out j.val =
          expandListModel xs level (decodedArray weights) j.val := by
  induction xs generalizing iter weights len level with
  | nil =>
      have hdropLe : iter.slice.val.length ≤ iter.i := by
        have hlen := congrArg List.length hdrop
        rw [List.length_drop] at hlen
        simp only [List.length_nil] at hlen
        have hzero : iter.slice.val.length - iter.i = 0 := by simpa using hlen
        exact (Nat.sub_eq_zero_iff_le.mp hzero)
      have hdone : ¬ iter.i < iter.slice.val.length := by omega
      refine ⟨weights, ?_, hweights, ?_⟩
      · rw [pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0.eq_def]
        dsimp only
        simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val,
          hdone, ↓reduceDIte, bind_tc_ok]
      · intro j
        rfl
  | cons x xs ih =>
      have hdropLength : (iter.slice.val.drop iter.i).length = xs.length + 1 := by
        rw [hdrop]
        simp
      have hstep : iter.i < iter.slice.val.length := by
        have := congrArg List.length hdrop
        simp at this
        omega
      have hnext := slice_next_step iter x xs hdrop
      have hdrop1 := slice_drop_step iter x xs hdrop
      have hx : Canonical x := hcoords x (by simp)
      have hprep := AspisR1.ExtractedMaskPreparedState.current_prepared_new x hx
      obtain ⟨prepared, hprepRun, hprepCanon⟩ := hprep
      have hdouble : 2 ^ level * 2 = 2 ^ (level + 1) := by
        rw [pow_succ]
      have hinnerCap : 2 * len.val ≤ N.val := by
        have hmono : 2 ^ (level + 1) ≤ 2 ^ (level + 1 + xs.length) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        calc
          2 * len.val = 2 ^ (level + 1) := by
            rw [hlen, ← hdouble]
            omega
          _ ≤ 2 ^ (level + 1 + xs.length) := hmono
          _ ≤ N.val := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcapacity
      have hdoubleBound : len.val * 2 < UScalar.size .Usize := by
        have hpowCap : 2 ^ (level + 1) ≤ N.val := by
          calc
            2 ^ (level + 1) = 2 * len.val := by rw [hlen, ← hdouble]; ring
            _ ≤ N.val := hinnerCap
        have hN : N.val < UScalar.size .Usize := by
          simpa only [UScalar.size] using N.hBounds
        rw [hlen]
        rw [hdouble]
        exact Nat.lt_of_le_of_lt hpowCap hN
      obtain ⟨len1, hlenmul, hlen1⟩ := usize_double len level hlen hdoubleBound
      let innerRange : AspisR1.ExtractedMaskReverseRange.ReverseRange :=
        ⟨{ start := 0#usize, «end» := len }⟩
      have hrange := range_rev_ok len
      obtain ⟨weights1, hinnerRun, hinnerCanon, hinnerModel⟩ :=
        selector_inner_loop_model innerRange weights prepared x len.val
          (by rfl) (by rfl) hinnerCap
          hweights hx hprepCanon
      have hinnerRun' :
          pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0
            ⟨{ start := 0#usize, «end» := len }⟩ weights prepared = .ok weights1 := by
        simpa [innerRange] using hinnerRun
      have htaildrop : ({iter with i := iter.i + 1}).slice.val.drop
          ({iter with i := iter.i + 1}).i = xs := by
        simpa using hdrop1
      have htailCapacity : 2 ^ (level + 1 + xs.length) ≤ N.val := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcapacity
      have htailCoords : ∀ y ∈ xs, Canonical y := by
        intro y hy
        exact hcoords y (by simp [hy])
      have htail := ih {iter with i := iter.i + 1} weights1 len1 (level+1)
        htaildrop (by simpa [hlen1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
        htailCapacity hinnerCanon htailCoords
      obtain ⟨out, htailRun, htailCanon, htailModel⟩ := htail
      refine ⟨out, ?_, htailCanon, ?_⟩
      · rw [pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0.eq_def]
        dsimp only
        simp only [hnext, bind_tc_ok, hprepRun, bind_tc_ok, hrange,
          bind_tc_ok, hinnerRun', bind_tc_ok, hlenmul, bind_tc_ok]
        exact htailRun
      · intro j
        rw [htailModel]
        have hinnerFun : decodedArray weights1 =
            selectorDescending (decode x) (2 ^ level) (decodedArray weights) := by
          funext k
          by_cases hk : k < N.val
          · simpa [hlen] using hinnerModel ⟨k, hk⟩
          · have hleft : decodedArray weights1 k = 0 := by
              simp [decodedArray, decodedAt, hk, weights1.property]
            have hright : selectorDescending (decode x) (2 ^ level)
                (decodedArray weights) k = 0 := by
              rw [selectorDescending_outside (decode x) (2 ^ level)
                (decodedArray weights) k N.val (by simpa [hlen] using hinnerCap)
                (by omega)]
              simp [decodedArray, decodedAt, hk, weights.property]
            rw [hleft, hright]
        rw [hinnerFun]
        rfl

private theorem initial_array_canonical {N : Usize} :
    canonicalArray (Array.repeat N field.QM31.ZERO) := by
  intro i
  simpa [Array.repeat_val] using zero_canonical

private theorem initial_decoded {N : Usize} :
    decodedArray (Array.repeat N field.QM31.ZERO) = fun _ => 0 := by
  have hz : decode field.QM31.ZERO = (0 : ExactQM) := by
    change AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ZERO = (0 : ExactQM)
    exact AspisR1.ExtractedMaskConstants.zero_decode
  funext j
  by_cases hj : j < N.val
  · simp [decodedArray, decodedAt, Array.repeat_val, hj, hz]
  · simp [decodedArray, decodedAt, hj]

/-- The generated `expand` wrapper succeeds and agrees with the list-level
symbolic expansion whenever every source coordinate is canonical and the
requested output capacity covers the power-of-two expansion. -/
theorem expand_model
    (N : Usize) (coordinates : Slice QM)
    (hcapacity : 2 ^ coordinates.val.length ≤ N.val)
    (hcoords : ∀ x ∈ coordinates.val, Canonical x) :
    ∃ out : Array QM N,
      pool_v1.pair_forest_copy_terminal.Selectors.expand N coordinates = .ok out ∧
      canonicalArray out ∧
      ∀ j : Fin N.val,
        decodedArray out j.val =
          expandListModel coordinates.val 0
            (fun i => if i = 0 then 1 else 0) j.val := by
  have hN : 1 ≤ N.val := by
    have hpow : 0 < 2 ^ coordinates.val.length := Nat.pow_pos (by omega)
    omega
  have hNpos : 0 < N.val := by omega
  let base : Array QM N := Array.repeat N field.QM31.ZERO
  obtain ⟨a, hupdate, hset⟩ :=
    array_update_success base 0#usize field.QM31.ONE (by simpa using hNpos)
  have hbaseCanonical : canonicalArray base := initial_array_canonical
  have honeCanonical : Canonical field.QM31.ONE := one_canonical
  have haCanonical : canonicalArray a := by
    simpa [hset] using set_canonical base 0#usize field.QM31.ONE
      hbaseCanonical honeCanonical (by simpa using hNpos)
  have hbaseDecode : decodedArray base = fun _ => 0 := initial_decoded
  have honeDecode' : decode field.QM31.ONE = (1 : ExactQM) := by
    change AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ONE = (1 : ExactQM)
    exact AspisR1.ExtractedMaskConstants.one_decode
  have hinit : decodedArray a = Function.update (fun _ => 0) 0 1 := by
    rw [hset, decodedArray_set_outer base 0#usize field.QM31.ONE
      (by simpa using hNpos), hbaseDecode]
    have hzeroIndex : (0#usize).val = 0 := rfl
    simp only [honeDecode', hzeroIndex]
  have hiter : SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      coordinates = .ok (⟨coordinates, 0⟩ : core.slice.iter.Iter QM) := rfl
  have hupdate' : Array.update (Array.repeat N field.QM31.ZERO)
      0#usize field.QM31.ONE = .ok a := by
    simpa [base] using hupdate
  obtain ⟨out, hrun, houtCanonical, houtModel⟩ :=
    expand_loop_model (⟨coordinates, 0⟩ : core.slice.iter.Iter QM) a 1#usize
      0 coordinates.val (by simp) rfl (by simpa using hcapacity) haCanonical hcoords
  refine ⟨out, ?_, houtCanonical, ?_⟩
  · rw [pool_v1.pair_forest_copy_terminal.Selectors.expand]
    simp only [hupdate', bind_tc_ok, hiter, bind_tc_ok]
    exact hrun
  · intro j
    have hstate : decodedArray a = (fun i => if i = 0 then 1 else 0) := by
      funext i
      rw [hinit]
      by_cases hz : i = 0 <;> simp [Function.update, hz]
    have hmodelInit := congrArg
      (fun w => expandListModel coordinates.val 0 w j.val) hstate
    rw [houtModel, hmodelInit]

#print axioms expand_loop_model
#print axioms expand_model
end AspisR1.SelectorExpansionOuter
