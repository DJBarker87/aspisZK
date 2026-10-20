import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4EqualityValueAdapterV5
import TerminalV4ReducerOpsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1.TerminalV4EqualityValueLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.TerminalV4EqualityValueAdapter

abbrev QM := AspisR1.TerminalV4EqualityValueAdapter.QM
abbrev ExactQM := AspisR1.TerminalV4EqualityValueAdapter.ExactQM
abbrev Canonical := AspisR1.TerminalV4EqualityValueAdapter.Canonical
abbrev Arr := Aeneas.Std.Array QM 10#usize

def factorAt (left right : Arr) (i : Fin 10) : ExactQM :=
  factor (decode (left.val[i.val]'(by simpa [left.property] using i.isLt)))
    (decode (right.val[i.val]'(by simpa [right.property] using i.isLt)))

def suffixProduct (left right : Arr) (k : Nat) : ExactQM :=
  ∏ i : Fin (10 - k), factorAt left right ⟨k + i.val, by omega⟩

private def factorNat (left right : Arr) (j : Nat) : ExactQM :=
  if h : j < 10 then factorAt left right ⟨j, h⟩ else 1

private theorem suffixProduct_eq_nat (left right : Arr) (k : Nat) :
    suffixProduct left right k =
      ∏ i : Fin (10 - k), factorNat left right (k + i.val) := by
  unfold suffixProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hj : k + i.val < 10 := by omega
  simp [factorNat, hj]

theorem suffixProduct_step (left right : Arr) (k : Nat) (hk : k < 10) :
    suffixProduct left right k =
      factorAt left right ⟨k, hk⟩ * suffixProduct left right (k + 1) := by
  rw [suffixProduct_eq_nat left right k]
  rw [suffixProduct_eq_nat left right (k + 1)]
  have hsize : 10 - k = (10 - (k + 1)) + 1 := by omega
  rw [hsize, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Nat.add_zero]
  have hfirst : factorNat left right k = factorAt left right ⟨k, hk⟩ := by
    simp [factorNat, hk]
  rw [hfirst]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Fin.val_succ]
  have hindex : k + (i.val + 1) = k + 1 + i.val := by omega
  rw [hindex]

private theorem array_index_usize_ok (a : Arr) (i : Usize)
    (hi : i.val < (10#usize : Usize).val) :
    Array.index_usize a i =
      .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [Array.getElem?_eq_getElem hidx]

theorem loop_fuel_success (left right : Arr) (acc : QM) (index : Usize)
    (n : Nat) (hfuel : index.val + n = 10)
    (hacc : Canonical acc)
    (hleft : ∀ i : Fin 10,
      Canonical (left.val[i.val]'(by simpa [left.property] using i.isLt)))
    (hright : ∀ i : Fin 10,
      Canonical (right.val[i.val]'(by simpa [right.property] using i.isLt))) :
    ∃ out : QM,
      pool_v1.pair_forest_semantic_terminal.equality_value_loop
          left right acc index = .ok out ∧
      Canonical out ∧
      decode out = decode acc * suffixProduct left right index.val := by
  induction n generalizing index acc with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hlen : (Slice.len (Array.to_slice left)).val = 10 := by
        rw [Slice.len_val, Array.length_to_slice]
        rfl
      have hstop : ¬ index < Slice.len (Array.to_slice left) := by
        rw [UScalar.lt_equiv]
        rw [hindex, hlen]
        omega
      refine ⟨acc, ?_, hacc, ?_⟩
      · rw [pool_v1.pair_forest_semantic_terminal.equality_value_loop]
        simp only [Aeneas.Std.lift, bind_tc_ok]
        rw [if_neg hstop]
      · have hzero : 10 - index.val = 0 := by omega
        rw [suffixProduct_eq_nat left right index.val, hzero,
          Fin.prod_univ_zero]
        simp
  | succ n ih =>
      have hindex_lt : index.val < 10 := by omega
      have hlen : (Slice.len (Array.to_slice left)).val = 10 := by
        rw [Slice.len_val, Array.length_to_slice]
        rfl
      have hguard : index < Slice.len (Array.to_slice left) := by
        rw [UScalar.lt_equiv]
        simpa [hlen] using hindex_lt
      let iLeft := left.val[index.val]'(by simpa [left.property] using hindex_lt)
      let iRight := right.val[index.val]'(by simpa [right.property] using hindex_lt)
      have hgetLeft : Array.index_usize left index = .ok iLeft := by
        exact array_index_usize_ok left index (by simpa using hindex_lt)
      have hgetRight : Array.index_usize right index = .ok iRight := by
        exact array_index_usize_ok right index (by simpa using hindex_lt)
      have hleftCanon : Canonical iLeft := by
        apply hleft ⟨index.val, by omega⟩
      have hrightCanon : Canonical iRight := by
        apply hright ⟨index.val, by omega⟩
      obtain ⟨f, hf, hfcanon, hfvalue⟩ :=
        equality_factor_call iLeft iRight hleftCanon hrightCanon
      obtain ⟨acc1, hmul, hacc1, hmulvalue⟩ :=
        AspisR1.TerminalV4QM31Exact.current_qm_mul_exact acc f hacc hfcanon
      have hsum : index.val + (1#usize : Usize).val <
          2 ^ UScalarTy.Usize.numBits := by
        scalar_tac
      obtain ⟨index1, hinc, hincval⟩ :=
        AspisR1.TerminalV4ReducerOps.tryMk_success
          (ty := .Usize) (index.val + (1#usize : Usize).val) hsum
      have hinc' : (index + 1#usize : Result Usize) = Result.ok index1 := by
        change UScalar.add index (1#usize) = Result.ok index1
        change UScalar.tryMk .Usize (index.val + (1#usize).val) = Result.ok index1
        exact hinc
      have hone : (1#usize : Usize).val = 1 := by rfl
      have hindex1 : index1.val + n = 10 := by
        rw [hincval, hone]
        omega
      obtain ⟨out, hrun, hout, hvalue⟩ :=
        ih acc1 index1 hindex1 hacc1
      refine ⟨out, ?_, hout, ?_⟩
      · rw [pool_v1.pair_forest_semantic_terminal.equality_value_loop]
        simp only [Aeneas.Std.lift, bind_tc_ok]
        rw [if_pos hguard]
        simp only [hgetLeft, hgetRight, hf, hmul, hinc', bind_tc_ok]
        exact hrun
      · have hfactor : decode f = factorAt left right ⟨index.val, by omega⟩ := by
          simpa [factorAt, iLeft, iRight, decode] using hfvalue
        have hvalue' : decode out =
            decode acc1 * suffixProduct left right (index.val + 1) := by
          simpa [hincval, hone] using hvalue
        have hmulvalue' : decode acc1 = decode acc * decode f := by
          simpa only [AspisR1.TerminalV4EqualityValueAdapter.decode] using hmulvalue
        rw [hvalue', hmulvalue', hfactor]
        rw [suffixProduct_step left right index.val (by omega)]
        ring

theorem suffixProduct_one_eq_fin9 (left right : Arr) :
    suffixProduct left right 1 =
      ∏ i : Fin 9, factorAt left right i.succ := by
  unfold suffixProduct
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

/-- Success and exact finite-product refinement for the actual generated
    wrapper. The only input obligations are canonicality of the ten cells;
    the generated wrapper itself supplies the initial factor and loop index. -/
theorem equality_value_success (left right : Arr)
    (hleft : ∀ i : Fin 10,
      Canonical (left.val[i.val]'(by simpa [left.property] using i.isLt)))
    (hright : ∀ i : Fin 10,
      Canonical (right.val[i.val]'(by simpa [right.property] using i.isLt))) :
    ∃ out : QM,
      pool_v1.pair_forest_semantic_terminal.equality_value left right = .ok out ∧
      Canonical out ∧
      decode out = factorAt left right ⟨0, by omega⟩ *
        (∏ i : Fin 9, factorAt left right i.succ) := by
  let q := left.val[0]'(by simpa [left.property])
  let q1 := right.val[0]'(by simpa [right.property])
  have hq : Array.index_usize left 0#usize = .ok q := by
    exact array_index_usize_ok left 0#usize (by simp)
  have hq1 : Array.index_usize right 0#usize = .ok q1 := by
    exact array_index_usize_ok right 0#usize (by simp)
  have hqcan : Canonical q := hleft ⟨0, by omega⟩
  have hq1can : Canonical q1 := hright ⟨0, by omega⟩
  obtain ⟨product, hfactor, hproduct, hfactorValue⟩ :=
    equality_factor_call q q1 hqcan hq1can
  have hloop := loop_fuel_success left right product 1#usize 9 (by decide)
    hproduct hleft hright
  obtain ⟨out, hrun, hout, hvalue⟩ := hloop
  refine ⟨out, ?_, hout, ?_⟩
  · rw [pool_v1.pair_forest_semantic_terminal.equality_value]
    simp only [hq, hq1, hfactor, bind_tc_ok]
    exact hrun
  · have honeval : (1#usize : Usize).val = 1 := by decide
    have hvalue' : decode out = decode product * suffixProduct left right 1 := by
      simpa [honeval] using hvalue
    have hinitial : decode product = factorAt left right ⟨0, by omega⟩ := by
      simpa [factorAt, q, q1, decode] using hfactorValue
    rw [hvalue', hinitial, suffixProduct_one_eq_fin9]

#print axioms AspisR1.TerminalV4EqualityValueLoop.loop_fuel_success
#print axioms AspisR1.TerminalV4EqualityValueLoop.equality_value_success

end AspisR1.TerminalV4EqualityValueLoop
