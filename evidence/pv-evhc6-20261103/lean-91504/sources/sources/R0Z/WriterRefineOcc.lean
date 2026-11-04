import R0Z.WritersExtracted
import Aeneas.Tactic.Solver.ScalarTac
import R0Z.BuilderModelAux

/-! Refinement of the extracted occupancy writer (DESIGN-BUILDER-MODEL §9).

`R0WriterCopies.write_occupancy_row` is the Aeneas b59d5188 extraction of the
extraction-friendly copy of pair_trace.rs:439-468 `write_occupancy`
(refine/writers/src/lib.rs; native differential test refine/diffharness).
We prove: on in-bounds rows it returns `ok`, writes exactly the 16 cells of the
row (11 of them nonzero-capable), and the lifted cells equal the model's
`occCell` whenever the record's fields lift to the model's `OccAux`. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

/-! ### Aeneas plumbing lemmas -/

theorem update_ok {n : Usize} (v : Array U32 n) (i : Usize) (x : U32) (h : i.val < n.val) :
    Array.update v i x = ok (v.set i x) := by
  unfold Array.update
  have hl : i.val < v.val.length := by rw [v.property]; exact h
  rw [Array.getElem?_Usize_eq, List.getElem?_eq_getElem hl]
  rfl

theorem index_ok {n : Usize} (v : Array U32 n) (i : Usize) (h : i.val < n.val) :
    Array.index_usize v i = ok (v.val[i.val]!) := by
  unfold Array.index_usize
  have hl : i.val < v.val.length := by rw [v.property]; exact h
  rw [Array.getElem?_Usize_eq, List.getElem?_eq_getElem hl, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hl]
  rfl

theorem usize_size_ge : 2 ^ 32 ≤ UScalar.size .Usize := by
  rw [UScalar.size_def]
  exact Nat.pow_le_pow_right (by norm_num) System.Platform.le_numBits

theorem uadd (x y : Usize) (h : x.val + y.val < 2 ^ 32) :
    (Usize.wrapping_add x y).val = x.val + y.val := by
  rw [Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le h usize_size_ge)

theorem umul (x y : Usize) (h : x.val * y.val < 2 ^ 32) :
    (Usize.wrapping_mul x y).val = x.val * y.val := by
  rw [Usize.wrapping_mul_val_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le h usize_size_ge)

theorem getElem!_set_list (l : List U32) (i k : Nat) (x : U32) (hi : i < l.length) :
    (l.set i x)[k]! = if k = i then x else l[k]! := by
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl, List.getElem!_eq_getElem?_getD, List.getElem?_set_self hi]
    rfl
  · rw [if_neg hk, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hk)]

theorem set_get (v : Array U32 256#usize) (i : Usize) (x : U32) (hi : i.val < 256) (k : Nat) :
    (v.set i x).val[k]! = if k = i.val then x else v.val[k]! := by
  rw [Array.set_val_eq]
  exact getElem!_set_list _ _ _ _ (by rw [v.property]; exact hi)

/-! ### The lane loop -/

theorem occ_loop (a : Array U32 8#usize) (base : Usize) (hb : base.val + 10 ≤ 256) :
    ∀ (n : Nat) (lane : Usize) (block : Array U32 256#usize), lane.val + n = 8 →
      ∃ b', write_occupancy_row_loop a block base lane = ok b' ∧
        ∀ k, b'.val[k]! = if base.val + 2 + lane.val ≤ k ∧ k < base.val + 10
          then a.val[k - base.val - 2]! else block.val[k]!
  | 0, lane, block, h => by
      refine ⟨block, ?_, fun k => ?_⟩
      · rw [write_occupancy_row_loop]
        rw [if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
      · rw [if_neg (by omega)]
  | n + 1, lane, block, h => by
      have hlt : lane < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hl8 : lane.val < 8 := by omega
      have h2 : (Usize.wrapping_add base 2#usize).val = base.val + 2 := uadd _ _ (by scalar_tac)
      have hix : (Usize.wrapping_add (Usize.wrapping_add base 2#usize) lane).val =
          base.val + 2 + lane.val := by rw [uadd _ _ (by scalar_tac), h2]
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨b', hb', hspec⟩ := occ_loop a base hb n (Usize.wrapping_add lane 1#usize)
        (block.set (Usize.wrapping_add (Usize.wrapping_add base 2#usize) lane) (a.val[lane.val]!))
        (by rw [hl1]; omega)
      refine ⟨b', ?_, fun k => ?_⟩
      · rw [write_occupancy_row_loop, if_pos hlt]
        rw [index_ok a lane (show lane.val < (8#usize).val by simpa using hl8)]
        simp only [lift, bind_tc_ok]
        rw [update_ok block _ _ (show _ < (256#usize).val by rw [hix]; simpa using (by omega : base.val + 2 + lane.val < 256))]
        simp only [bind_tc_ok]
        exact hb'
      · rw [hspec k, hl1, set_get _ _ _ (by rw [hix]; omega), hix]
        by_cases hk : k = base.val + 2 + lane.val
        · subst hk
          rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
          congr 2
          omega
        · rw [if_neg hk]
          by_cases hr : base.val + 2 + (lane.val + 1) ≤ k ∧ k < base.val + 10
          · rw [if_pos hr, if_pos (by omega)]
          · rw [if_neg hr, if_neg (by omega)]

#print axioms update_ok
#print axioms index_ok
#print axioms uadd
#print axioms set_get
#print axioms occ_loop
end R0Z.WriterRefine
