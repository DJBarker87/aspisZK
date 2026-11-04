import R0Z.WriterRefineValue

/-! The extracted value-aux writer, outer loop over the three values
(DESIGN-BUILDER-MODEL §9). -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

/-- Which value (0, 1, 2) owns local row r; 3 = none. -/
def jOf (r : Nat) : Nat :=
  if r = 0 then 0 else if r = 1 then 0 else if r = 12 then 0
  else if r = 2 then 1 else if r = 3 then 1 else if r = 14 then 1
  else if r = 4 then 2 else if r = 5 then 2 else if r = 8 then 2 else 3

/-- The value cells written by values j0..2 over a block `blk`. -/
def OuterVal (vals : Nat → Nat) (j0 : Nat) (blk : Nat → Nat) (k : Nat) : Nat :=
  if jOf (k / 16) < 3 ∧ j0 ≤ jOf (k / 16) then
    (if k % 16 < 10 then vals (jOf (k / 16)) / 2 ^ tOf (2 * jOf (k / 16)) k % 2
     else if k % 16 = 10 ∧ k / 16 = 2 * jOf (k / 16) then vals (jOf (k / 16)) else blk k)
  else blk k

theorem rowJ (j r : Nat) (hj : j < 3) :
    (r = 2 * j ∨ r = 2 * j + 1 ∨ r = xr (2 * j)) ↔ jOf r = j := by
  by_cases hr : r < 15
  · interval_cases r <;> interval_cases j <;> decide
  · have h3 : jOf r = 3 := by
      unfold jOf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hx : xr (2 * j) ≤ 14 := by unfold xr; split_ifs <;> omega
    rw [h3]
    constructor
    · intro h; omega
    · intro h; omega

theorem inRows_iff (j k : Nat) (hj : j < 3) :
    InRows (2 * j) k ↔ jOf (k / 16) = j ∧ k % 16 < 10 := by
  unfold InRows
  rw [rowJ j (k / 16) hj]

theorem jOf_base (j : Nat) (hj : j < 3) : jOf (2 * j) = j := by
  unfold jOf; interval_cases j <;> rfl

theorem value_outer (values : Array U32 3#usize) :
    ∀ (n : Nat) (j : Usize) (block : Array U32 256#usize), j.val + n = 3 →
      ∃ b', write_value_block_loop0 values block j = ok b' ∧
        ∀ k, (b'.val[k]!).val =
          OuterVal (fun i => (values.val[i]!).val) j.val (fun k => (block.val[k]!).val) k
  | 0, j, block, h => by
      refine ⟨block, ?_, fun k => ?_⟩
      · rw [write_value_block_loop0, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
      · unfold OuterVal; rw [if_neg (by omega)]
  | n + 1, j, block, h => by
      have hj3 : j.val < 3 := by omega
      have hlt : j < 3#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have h2j : (Usize.wrapping_mul 2#usize j).val = 2 * j.val := umul _ _ (by simp; omega)
      have hbase : (Usize.wrapping_mul 2#usize j).val = 0 ∨ (Usize.wrapping_mul 2#usize j).val = 2 ∨
          (Usize.wrapping_mul 2#usize j).val = 4 := by rw [h2j]; omega
      have h16 : (Usize.wrapping_mul (Usize.wrapping_mul 2#usize j) 16#usize).val = 2 * j.val * 16 :=
        by rw [umul _ _ (by rw [h2j]; simp; omega), h2j]; simp
      have h10 : (Usize.wrapping_add (Usize.wrapping_mul (Usize.wrapping_mul 2#usize j) 16#usize)
          10#usize).val = 2 * j.val * 16 + 10 := by rw [uadd _ _ (by rw [h16]; simp; omega), h16]; simp
      have hj1 : (Usize.wrapping_add j 1#usize).val = j.val + 1 := uadd _ _ (by scalar_tac)
      have hi10 : (Usize.wrapping_add (Usize.wrapping_mul (Usize.wrapping_mul 2#usize j) 16#usize)
          10#usize).val < (256#usize).val := by rw [h10]; simp; omega
      let raw := values.val[j.val]!
      obtain ⟨b1, hb1, hs1⟩ := value_inner raw (Usize.wrapping_mul 2#usize j) hbase 30 0#u32 block
        (by simp)
      obtain ⟨b', hb', hs⟩ := value_outer values n (Usize.wrapping_add j 1#usize)
        (b1.set (Usize.wrapping_add (Usize.wrapping_mul (Usize.wrapping_mul 2#usize j) 16#usize)
          10#usize) raw) (by rw [hj1]; omega)
      refine ⟨b', ?_, fun k => ?_⟩
      · rw [write_value_block_loop0, if_pos hlt, index_ok values j (by simpa using hj3)]
        simp only [bind_tc_ok, lift]
        rw [hb1]
        simp only [bind_tc_ok]
        rw [update_ok b1 _ _ hi10]
        simp only [bind_tc_ok]
        exact hb'
      · have ha : ∀ k, ((b1.set (Usize.wrapping_add (Usize.wrapping_mul (Usize.wrapping_mul 2#usize j)
            16#usize) 10#usize) raw).val[k]!).val = (if k = 2 * j.val * 16 + 10 then raw.val else
            (if InRows (2 * j.val) k then raw.val / 2 ^ tOf (2 * j.val) k % 2 else (block.val[k]!).val)) := by
          intro k
          rw [set_get' b1 _ _ hi10 k, h10]
          split
          · rfl
          · rw [hs1 k, h2j]
            simp only [show (0#u32 : U32).val = 0 by simp, Nat.zero_le, and_true]
        rw [hs k, hj1]
        unfold OuterVal
        simp only [ha]
        have f1 := inRows_iff j.val k hj3
        have hraw : raw.val = (values.val[j.val]!).val := rfl
        simp only [f1, hraw]
        by_cases hk : jOf (k / 16) = j.val
        · simp only [hk, true_and, le_refl, and_true]
          split_ifs <;> first | rfl | omega
        · have nk : ¬ k = 2 * j.val * 16 + 10 := by
            intro e; apply hk; rw [e, show (2 * j.val * 16 + 10) / 16 = 2 * j.val by omega]
            exact jOf_base _ hj3
          simp only [hk, nk, false_and, if_false]
          split_ifs <;> first | rfl | omega

#print axioms rowJ
#print axioms inRows_iff
#print axioms value_outer
end R0Z.WriterRefine
