import SelectorValueLaneIndexedSlice
import SelectorReconstructIndexedSource
import SelectorExpansionCorrectness
import ExtractedMaskQM31Exact
import ExtractedMaskReducerOps

/-! Source proof for the candidate v3 indexed `add_value_lanes_loop3`: each
cell from the starting index through 32 is multiplied by the fixed selector;
earlier cells are preserved. Success and canonicality are derived from the
actual generated calls, not assumed. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneIndexedLoop3

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReducerOps
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev Loop3 := AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3

private def cellAt (a : Array QM 33#usize) (j : Nat) : QM :=
  if h : j < 33 then a.val[j]'(by simpa [a.property] using h)
  else field.QM31.ZERO

/-- The loop's Nat-indexed view is the ordinary Array cell at every valid
33-cell index. This exposes the exact observation used by the output-list map. -/
theorem cellAt_eq_getElem (a : Array QM 33#usize) (j : Fin 33) :
    cellAt a j.val = a.val[j.val]'(by simpa [a.property] using j.isLt) := by
  simp [cellAt, j.isLt]

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem update_success {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α) (hi : i.val < n.val) :
    ∃ out : Array α n, Array.update a i x = .ok out ∧ out = a.set i x := by
  obtain ⟨out, hr, hs⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  exact ⟨out, hr, hs⟩

private theorem set_canonical {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (ha : AspisR1.SelectorExpansionCorrectness.canonicalArray a)
    (hx : Canonical x) : AspisR1.SelectorExpansionCorrectness.canonicalArray (a.set i x) := by
  intro j
  have hj0 : j.val < a.val.length := by simpa using j.isLt
  have hjSet : j.val < (a.val.set i.val x).length := by simpa using hj0
  change Canonical ((a.val.set i.val x)[j.val]'hjSet)
  by_cases heq : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjSet)
      simpa [heq] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = a.val[j.val]'hj0 := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        heq hjSet)
    rw [hcell]
    exact ha j

private theorem cellAt_set {a : Array QM 33#usize} {i : Usize} {x : QM}
    (hi : i.val < 33) (j : Nat) :
    cellAt (a.set i x) j = if j = i.val then x else cellAt a j := by
  by_cases hj : j < 33
  · by_cases hEq : j = i.val
    · subst j
      simp [cellAt, hj, Array.set_val_eq]
    · have hne : i.val ≠ j := Ne.symm hEq
      have hjSet : j < (a.val.set i.val x).length := by simpa [a.property] using hj
      have hjA : j < a.val.length := by simpa [a.property] using hj
      have hcell := List.getElem_set_ne (l := a.val) (i := i.val) (j := j) hne hjSet
      simp [cellAt, hj, Array.set_val_eq, hEq, hcell, hjA]
  · have hne : j ≠ i.val := by omega
    simp [cellAt, hj, Array.set_val_eq, hne]

private theorem small_usize_bound (n : Nat) (hn : n < 1024) :
    n < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
  have hmax := Usize.cMax_bound_concrete.1
  omega

private theorem increment_success (i : Usize) (hi : i.val < 33) :
    ∃ i1 : Usize, (i + 1#usize : Result Usize) = .ok i1 ∧ i1.val = i.val + 1 := by
  have hbound : i.val + 1 < 2 ^ UScalarTy.Usize.numBits := by
    apply small_usize_bound
    omega
  obtain ⟨i1, hrun, hval⟩ := tryMk_success (ty := .Usize) (i.val + 1) hbound
  have hresult : (i + 1#usize : Result Usize) = .ok i1 := by
    change UScalar.add i 1#usize = .ok i1
    simpa [UScalar.add] using hrun
  exact ⟨i1, hresult, hval⟩

/-- At fuel `fuel`, the indexed generated loop returns a canonical array and
implements the exact prefix-preserving pointwise multiplication equation. -/
theorem add_value_lanes_loop3_success_fuel
    (selector : QM) (range : Array QM 33#usize) (i : Usize) (fuel : Nat)
    (hspan : i.val + fuel = 33)
    (hselector : Canonical selector)
    (hrange : AspisR1.SelectorExpansionCorrectness.canonicalArray range) :
    ∃ out, Loop3 selector range i = .ok out ∧
      AspisR1.SelectorExpansionCorrectness.canonicalArray out ∧
      ∀ j : Fin 33, decode (cellAt out j.val) =
        if j.val < i.val then decode (cellAt range j.val)
        else decode selector * decode (cellAt range j.val) := by
  induction fuel generalizing range i with
  | zero =>
      have hi : i.val = 33 := by omega
      have hstop : ¬ i < 33#usize := by
        rw [UScalar.lt_equiv]
        simp [hi]
      refine ⟨range, ?_, hrange, ?_⟩
      · change AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
          selector range i = .ok range
        rw [AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3.eq_def]
        simp only [if_neg hstop]
      · intro j
        have hj : j.val < 33 := j.isLt
        simp [hi, hj, cellAt]
  | succ fuel ih =>
      have hbound : i.val < 33 := by omega
      have hlt : i < 33#usize := by
        apply (UScalar.lt_equiv i 33#usize).2
        exact hbound
      let q := cellAt range i.val
      have hqEq : q = range.val[i.val]'(by simpa [range.property] using hbound) := by
        simp [q, cellAt, hbound]
      have hread : Array.index_usize range i = .ok q := by
        rw [index_usize_ok range i hbound, ← hqEq]
      have hq : Canonical q := by
        simpa [q, cellAt, hbound] using
          hrange ⟨i.val, by simpa [range.property] using hbound⟩
      obtain ⟨product, hmul, hproduct, hproductDecode⟩ :=
        current_qm_mul_exact selector q hselector hq
      have hupdateBound : i.val < (33#usize).val := by
        simpa using hbound
      obtain ⟨range1, hupdate, hset⟩ := update_success range i product hupdateBound
      have hrange1 : AspisR1.SelectorExpansionCorrectness.canonicalArray range1 := by
        rw [hset]
        exact set_canonical range i product hrange hproduct
      obtain ⟨i1, hinc, hincVal⟩ := increment_success i hbound
      have hspan1 : i1.val + fuel = 33 := by omega
      obtain ⟨out, hrun, houtCanonical, hvalues⟩ :=
        ih range1 i1 hspan1 hrange1
      refine ⟨out, ?_, houtCanonical, ?_⟩
      · change AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
          selector range i = .ok out
        rw [AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3.eq_def]
        simp only [if_pos hlt, hread, bind_tc_ok, hmul, bind_tc_ok,
          hupdate, bind_tc_ok, hinc, bind_tc_ok]
        exact hrun
      · intro j
        have hvaluesj := hvalues j
        rw [hvaluesj]
        rw [hset]
        rw [cellAt_set hbound j.val]
        by_cases hj : j.val < i.val
        · have hj1 : j.val < i1.val := by omega
          have hne : j.val ≠ i.val := by omega
          simp [hj, hj1, hne]
        · by_cases heq : j.val = i.val
          · have hj1 : j.val < i1.val := by omega
            have hnot : ¬ i1.val ≤ j.val := by omega
            have hcell : cellAt range j.val = q := by simp [q, heq]
            rw [hcell]
            by_cases hle : i1.val ≤ j.val
            · exact (hnot hle).elim
            · simp [hj, hj1, heq, hle, hproductDecode]
              intro hle'
              omega
          · have hi1 : i1.val ≤ j.val := by omega
            have hne : j.val ≠ i.val := heq
            simp [hj, hne, hi1]

/-- The generated 33-cell wrapper case needed by the terminal composition. -/
theorem add_value_lanes_loop3_from_zero
    (selector : QM) (range : Array QM 33#usize)
    (hselector : Canonical selector)
    (hrange : AspisR1.SelectorExpansionCorrectness.canonicalArray range) :
    ∃ out, Loop3 selector range 0#usize = .ok out ∧
      AspisR1.SelectorExpansionCorrectness.canonicalArray out ∧
      ∀ j : Fin 33, decode (cellAt out j.val) =
        decode selector * decode (cellAt range j.val) := by
  obtain ⟨out, hrun, hcanonical, hvalues⟩ :=
    add_value_lanes_loop3_success_fuel selector range 0#usize 33 (by norm_num)
      hselector hrange
  refine ⟨out, hrun, hcanonical, ?_⟩
  intro j
  simpa using hvalues j

#print axioms cellAt_eq_getElem
#print axioms add_value_lanes_loop3_success_fuel
#print axioms add_value_lanes_loop3_from_zero
end AspisR1.SelectorValueLaneIndexedLoop3
