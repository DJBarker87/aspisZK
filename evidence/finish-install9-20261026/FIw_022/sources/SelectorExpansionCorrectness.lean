import SelectorSourceSlice
import ExtractedMaskReverseRange
import ExtractedMaskPreparedState
import ExtractedMaskPreparedMul
import ExtractedMaskTowerAdd
import ExtractedMaskQM31Exact
import EqualityValueAdapter
import ExtractedMaskReducerOps
import ExtractedMaskHornerStep

/-! Actual selected-selector expansion contracts.  The model below is the
literal descending two-store recurrence from `SelectedSelectorExpansion`, but
the theorems in this file connect its individual stores to the generated
Aeneas loop.  No caller-supplied success/output equality is used. -/
set_option autoImplicit false
namespace AspisR1.SelectorExpansionCorrectness

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReverseRange
open AspisR1.ExtractedMaskPreparedState
open AspisR1.ExtractedMaskPreparedMul
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def decode (x : QM) : ExactQM := AspisR1.ExtractedMaskQM31Exact.decode x

def canonicalArray {n : Usize} (a : Array QM n) : Prop :=
  ∀ i : Fin n.val, Canonical (a.val[i.val]'(by simpa [a.property] using i.isLt))

def decodedAt {n : Usize} (a : Array QM n) (i : Nat) : ExactQM :=
  if h : i < n.val then decode (a.val[i]'(by simpa [a.property] using h)) else 0

def selectorFactor (x : ExactQM) (odd : Bool) : ExactQM :=
  if odd then x else 1 - x

/-- One source iteration reads the parent before either of its two writes. -/
def selectorWrite (x : ExactQM) (i : Nat) (w : Nat → ExactQM) : Nat → ExactQM :=
  let parent := w i
  let right := x * parent
  Function.update (Function.update w (2*i) (parent - right)) (2*i+1) right

def selectorDescending (x : ExactQM) : Nat → (Nat → ExactQM) → Nat → ExactQM
  | 0, w, j => w j
  | n+1, w, j => selectorDescending x n (selectorWrite x n w) j

theorem selectorWrite_below (x : ExactQM) (i j : Nat)
    (h : j < i) (w : Nat → ExactQM) : selectorWrite x i w j = w j := by
  have h0 : j ≠ 2*i := by omega
  have h1 : j ≠ 2*i+1 := by omega
  simp [selectorWrite, h0, h1]

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem array_update_success {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α) (hi : i.val < n.val) :
    ∃ out : Array α n, Array.update a i x = .ok out ∧ out = a.set i x := by
  obtain ⟨out, hr, hs⟩ := WP.spec_imp_exists (Array.update_spec a i x (by simpa [a.property] using hi))
  exact ⟨out, hr, hs⟩

private theorem set_canonical {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (ha : canonicalArray a) (hx : Canonical x) : canonicalArray (a.set i x) := by
  intro j
  have hj : j.val < (a.set i x).val.length := by simpa using j.isLt
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

def decodedArray {n : Usize} (a : Array QM n) : Nat → ExactQM := decodedAt a

private theorem decodedArray_set {n : Usize} (a : Array QM n) (i : Usize)
    (x : QM) (hi : i.val < n.val) :
    decodedArray (a.set i x) =
      Function.update (decodedArray a) i.val (decode x) := by
  funext j
  by_cases hj : j < n.val
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

private theorem usize_mul2 (i : Usize) (hi : 2*i.val < 2^UScalarTy.Usize.numBits) :
    ∃ twice : Usize, UScalar.mul 2#usize i = .ok twice ∧ twice.val = 2*i.val := by
  obtain ⟨twice, hmul, hval⟩ := AspisR1.ExtractedMaskReducerOps.tryMk_success (2*i.val) hi
  exact ⟨twice, by simpa [UScalar.mul] using hmul, hval⟩

private theorem usize_add1 (i : Usize) (hi : i.val+1 < 2^UScalarTy.Usize.numBits) :
    ∃ next : Usize, UScalar.add i 1#usize = .ok next ∧ next.val = i.val+1 := by
  obtain ⟨next, hadd, hval⟩ := AspisR1.ExtractedMaskReducerOps.tryMk_success (i.val+1) hi
  exact ⟨next, by simpa [UScalar.add] using hadd, hval⟩

private theorem source_inner_step
    {N : Usize} (iter : ReverseRange) (weights : Array QM N) (prepared : Prepared)
    (x : QM) (n : Nat)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val = n+1)
    (hn : 2*(n+1) ≤ N.val)
    (hweights : canonicalArray weights) (hx : Canonical x)
    (hprepared : PreparedFor prepared x) :
    ∃ iter1 : ReverseRange, ∃ out : Array QM N,
      pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter weights prepared =
        pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter1 out prepared ∧
      iter1.iter.start.val = 0 ∧ iter1.iter.end.val = n ∧
      canonicalArray out ∧
      ∀ j : Fin N.val,
        decodedArray out j.val =
          selectorWrite (decode x) n (decodedArray weights) j.val := by
  have hstep : iter.iter.start.val < iter.iter.end.val := by omega
  have hendpos : 1 ≤ iter.iter.end.val := by omega
  have hindexVal : (Usize.wrapping_sub iter.iter.end 1#usize).val = n := by
    rw [AspisR1.ExtractedMaskReverseRange.wrapping_sub_one_val _ hendpos]
    omega
  let index := Usize.wrapping_sub iter.iter.end 1#usize
  have hi : index.val < N.val := by rw [hindexVal]; omega
  let parent := weights.val[index.val]'(by simpa [weights.property] using hi)
  have hread : Array.index_usize weights index = .ok parent := by
    exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok weights index hi
  have hparent : Canonical parent := by
    have hp := hweights ⟨index.val, by simpa [weights.property] using hi⟩
    simpa [parent] using hp
  obtain ⟨right, hright, hrightCanon, hrightValue⟩ :=
    AspisR1.ExtractedMaskPreparedMul.prepared_mul_exact prepared x parent
      hx hparent hprepared
  obtain ⟨left, hleft, hleftCanon, hleftValue⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact parent right hparent hrightCanon
  have hleftBound : 2*n < N.val := by omega
  have hrightBound : 2*n+1 < N.val := by omega
  let iter1 : ReverseRange :=
    ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
  have hNbound : N.val < 2^UScalarTy.Usize.numBits := N.hBounds
  have hleftValueSize : 2*n < 2^UScalarTy.Usize.numBits := by omega
  have hrightValueSize : 2*n+1 < 2^UScalarTy.Usize.numBits := by omega
  let leftIndex : Usize := UScalar.ofNatCore (2*n) hleftValueSize
  have hleftIndexVal : leftIndex.val = 2*n := by simp [leftIndex]
  have hleftIndex' : UScalar.mul 2#usize index = .ok leftIndex := by
    obtain ⟨twice, hmul, hv⟩ := usize_mul2 index (by rw [hindexVal]; omega)
    have hval' : twice.val = leftIndex.val := by
      calc
        twice.val = 2 * index.val := hv
        _ = 2*n := by rw [hindexVal]
        _ = leftIndex.val := by simp [leftIndex]
    have heq : twice = leftIndex := UScalar.eq_of_val_eq hval'
    exact hmul.trans (congrArg Result.ok heq)
  let rightIndex : Usize := UScalar.ofNatCore (2*n+1) hrightValueSize
  have hrightIndexVal : rightIndex.val = 2*n+1 := by simp [rightIndex]
  have hrightIndex' : UScalar.add leftIndex 1#usize = .ok rightIndex := by
    obtain ⟨next, hadd, hv⟩ := usize_add1 leftIndex (by omega)
    have hval' : next.val = rightIndex.val := by
      calc
        next.val = leftIndex.val + 1 := hv
        _ = 2*n+1 := by rw [hleftIndexVal]
        _ = rightIndex.val := by simp [rightIndex]
    have heq : next = rightIndex := UScalar.eq_of_val_eq hval'
    exact hadd.trans (congrArg Result.ok heq)
  obtain ⟨out1, hupdate1, hset1⟩ :=
    array_update_success weights leftIndex left (by simpa [hleftIndexVal] using hleftBound)
  obtain ⟨out, hupdate2, hset2⟩ :=
    array_update_success out1 rightIndex right (by simpa [hrightIndexVal] using hrightBound)
  have hcanonical1 : canonicalArray out1 := by
    rw [hset1]
    exact set_canonical weights leftIndex left hweights hleftCanon
  have hcanonical : canonicalArray out := by
    rw [hset2]
    exact set_canonical out1 rightIndex right hcanonical1 hrightCanon
  have hleftIndexSource :
      (2#usize * Usize.wrapping_sub iter.iter.end 1#usize : Result Usize) = .ok leftIndex := by
    change UScalar.mul 2#usize (Usize.wrapping_sub iter.iter.end 1#usize) = .ok leftIndex
    exact hleftIndex'
  have hrightIndexSource :
      (leftIndex + 1#usize : Result Usize) = .ok rightIndex := by
    change UScalar.add leftIndex 1#usize = .ok rightIndex
    exact hrightIndex'
  have hrec :
      pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter weights prepared =
        pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter1 out prepared := by
    rw [pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0.eq_def]
    dsimp only
    simp only [reverse_next_step iter hstep, bind_tc_ok, index, parent,
      hread, hright, hleft, hleftIndexSource, hupdate1, hrightIndexSource,
      hupdate2, iter1, bind_tc_ok]
  have hstart1 : iter1.iter.start.val = 0 := by simpa [iter1] using hstart
  have hend1 : iter1.iter.end.val = n := by
    dsimp [iter1]
    rw [AspisR1.ExtractedMaskReverseRange.wrapping_sub_one_val _ hendpos]
    omega
  refine ⟨iter1, out, hrec, hstart1, hend1, hcanonical, ?_⟩
  intro j
  have hfun1 : decodedArray out1 =
      Function.update (decodedArray weights) (2*n) (decode left) := by
    simpa [leftIndex, hleftIndexVal, hset1] using
      decodedArray_set weights leftIndex left (by simpa [hleftIndexVal] using hleftBound)
  have hfun2 : decodedArray out =
      Function.update (decodedArray out1) (2*n+1) (decode right) := by
    simpa [rightIndex, hrightIndexVal, hset2] using
      decodedArray_set out1 rightIndex right (by simpa [hrightIndexVal] using hrightBound)
  have hparentValue : decodedArray weights index.val = decode parent := by
    simp [decodedArray, decodedAt, hi, parent]
  have hparentN : decodedArray weights n = decode parent := by
    rw [← hindexVal]
    exact hparentValue
  have hleftValue' : decode left = decode parent - decode right := by
    change AspisR1.ExtractedMaskQM31Exact.decode left =
      AspisR1.ExtractedMaskQM31Exact.decode parent -
        AspisR1.ExtractedMaskQM31Exact.decode right at hleftValue
    exact hleftValue
  have hrightValue' : decode right = decode x * decode parent := by
    simpa [decode] using hrightValue
  rw [hfun2, hfun1]
  by_cases h0 : j.val = 2*n
  · have hnot : j.val ≠ 2*n+1 := by omega
    simp [Function.update, selectorWrite, h0, hnot,
      hleftValue', hrightValue', hparentN]
  · by_cases h1 : j.val = 2*n+1
    · simp [Function.update, selectorWrite, h1, h0,
        hleftValue', hrightValue', hparentN]
    · simp [Function.update, selectorWrite, h0, h1]

theorem selector_inner_loop_model
    {N : Usize} (iter : ReverseRange) (weights : Array QM N) (prepared : Prepared)
    (x : QM) (n : Nat)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val = n)
    (hn : 2*n ≤ N.val)
    (hweights : canonicalArray weights) (hx : Canonical x)
    (hprepared : PreparedFor prepared x) :
    ∃ out : Array QM N,
      pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter weights prepared =
        .ok out ∧ canonicalArray out ∧
      ∀ j : Fin N.val,
        decodedArray out j.val = selectorDescending (decode x) n
          (decodedArray weights) j.val := by
  induction n generalizing iter weights hstart hweights with
  | zero =>
      have hstop : iter.iter.end.val ≤ iter.iter.start.val := by omega
      refine ⟨weights, ?_, hweights, ?_⟩
      · rw [pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0.eq_def]
        simp only [reverse_next_done iter hstop, bind_tc_ok]
      · intro j
        rfl
  | succ n ih =>
      obtain ⟨iter1, out1, hstep, hstart1, hend1, hcanonical1, hmodel1⟩ :=
        source_inner_step iter weights prepared x n hstart hend (by omega)
          hweights hx hprepared
      have hrec := ih iter1 out1 hstart1 hend1 (by omega) hcanonical1
      obtain ⟨out, hrun, hcanonical, hmodel⟩ := hrec
      refine ⟨out, ?_, hcanonical, ?_⟩
      · rw [hstep]
        exact hrun
      · intro j
        rw [hmodel]
        have hmodel1' : decodedArray out1 =
            selectorWrite (decode x) n (decodedArray weights) := by
          funext k
          by_cases hk : k < N.val
          · exact hmodel1 ⟨k, hk⟩
          · have hout : decodedArray out1 k = 0 := by
              simp [decodedArray, decodedAt, hk, out1.property]
            have hweights0 : decodedArray weights k = 0 := by
              simp [decodedArray, decodedAt, hk, weights.property]
            have hk0 : k ≠ 2*n := by omega
            have hk1 : k ≠ 2*n+1 := by omega
            rw [hout]
            simp [selectorWrite, Function.update, hk0, hk1, hweights0]
        rw [hmodel1']
        rfl


/-! This establishes the actual inner-loop array/write correspondence. The
remaining bridge to `boxed_at_point` is the outer forward slice traversal and
the two fixed range slices; these are not premises of the theorem above. -/

#print axioms selectorWrite_below
#print axioms decodedArray_set
#print axioms source_inner_step
#print axioms selector_inner_loop_model

end AspisR1.SelectorExpansionCorrectness
