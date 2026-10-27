import R0Z.NodeRefine

/-! B3 (b): the relocation read-back (pair_forest_trace.rs:216-224) inverts the
node writer: reading a node block written from (left, right) after a block
whose row 11 is `prev` returns exactly (prev[0..8], left, right). -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result

theorem read_back_loop_spec (prev row0 row12 : Array U32 16#usize)
    (h15 : (row0.val[15]!).val < 2147483647) :
    ∀ (n : Nat) (lane : Usize) (cur l r : Array U32 8#usize), lane.val + n = 8 →
      ∃ c' l' r', R0BlockCopies.read_back_loop prev row0 row12 cur l r lane = ok (c', l', r') ∧
        ∀ k, (c'.val[k]! = if lane.val ≤ k ∧ k < 8 then prev.val[k]! else cur.val[k]!) ∧
          (l'.val[k]! = if lane.val ≤ k ∧ k < 8 then row12.val[k]! else l.val[k]!) ∧
          ((r'.val[k]!).val = if lane.val ≤ k ∧ k < 8 then
            (if k = 7 then (if 1095962629 ≤ (row0.val[15]!).val then (row0.val[15]!).val - 1095962629
              else (row0.val[15]!).val + 2147483647 - 1095962629) else (row0.val[8 + k]!).val)
            else (r.val[k]!).val)
  | 0, lane, cur, l, r, h => by
      refine ⟨cur, l, r, ?_, fun k => ⟨by rw [if_neg (by omega)], by rw [if_neg (by omega)],
        by rw [if_neg (by omega)]⟩⟩
      rw [R0BlockCopies.read_back_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lane, cur, l, r, h => by
      have hlt : lane < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : lane.val < (8#usize).val := by simp; omega
      have hb16 : lane.val < (16#usize).val := by simp; omega
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨z, hz, hzv⟩ := m31_sub_spec_wide (row0.val[15]!) R0BlockCopies.TWEAK h15
        (by rw [tval]; norm_num)
      rw [tval] at hzv
      have tail : ∀ v : U32, v.val = (if lane.val = 7 then (if 1095962629 ≤ (row0.val[15]!).val
            then (row0.val[15]!).val - 1095962629 else (row0.val[15]!).val + 2147483647 - 1095962629)
            else (row0.val[8 + lane.val]!).val) →
          ∃ c' l' r', R0BlockCopies.read_back_loop prev row0 row12 (cur.set lane (prev.val[lane.val]!))
            (l.set lane (row12.val[lane.val]!)) (r.set lane v) (Usize.wrapping_add lane 1#usize) = ok (c', l', r') ∧
          ∀ k, (c'.val[k]! = if lane.val ≤ k ∧ k < 8 then prev.val[k]! else cur.val[k]!) ∧
            (l'.val[k]! = if lane.val ≤ k ∧ k < 8 then row12.val[k]! else l.val[k]!) ∧
            ((r'.val[k]!).val = if lane.val ≤ k ∧ k < 8 then
              (if k = 7 then (if 1095962629 ≤ (row0.val[15]!).val then (row0.val[15]!).val - 1095962629
                else (row0.val[15]!).val + 2147483647 - 1095962629) else (row0.val[8 + k]!).val)
              else (r.val[k]!).val) := by
        intro v hvv
        obtain ⟨c', l', r', hok, hs⟩ := read_back_loop_spec prev row0 row12 h15 n (Usize.wrapping_add lane 1#usize)
          (cur.set lane (prev.val[lane.val]!)) (l.set lane (row12.val[lane.val]!)) (r.set lane v) (by rw [hl1]; omega)
        refine ⟨c', l', r', hok, fun k => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hs k
        rw [hl1] at h1 h2 h3
        refine ⟨?_, ?_, ?_⟩
        · rw [h1, set_get' cur lane _ hb k]
          split_ifs <;> first | rfl | omega | (subst_vars; rfl)
        · rw [h2, set_get' l lane _ hb k]
          split_ifs <;> first | rfl | omega | (subst_vars; rfl)
        · rw [h3, set_get' r lane _ hb k]
          by_cases e : k = lane.val
          · rw [if_neg (by omega), if_pos e, if_pos (show lane.val ≤ k ∧ k < 8 by omega), hvv, e]
          · rw [if_neg e]
            by_cases a : lane.val + 1 ≤ k ∧ k < 8
            · rw [if_pos a, if_pos (show lane.val ≤ k ∧ k < 8 by omega)]
            · rw [if_neg a, if_neg (show ¬ (lane.val ≤ k ∧ k < 8) by omega)]
      rw [R0BlockCopies.read_back_loop, if_pos hlt, index_ok prev lane hb16]
      simp only [bind_tc_ok]
      rw [update_ok cur lane _ hb, index_ok row12 lane hb16]
      simp only [bind_tc_ok]
      rw [update_ok l lane _ hb]
      simp only [bind_tc_ok]
      by_cases e7 : lane = 7#usize
      · have e7' : lane.val = 7 := by rw [e7]; simp
        rw [if_pos e7, index_ok row0 15#usize (by simp)]
        simp only [bind_tc_ok, show (15#usize : Usize).val = 15 by simp]
        rw [hz]
        simp only [bind_tc_ok]
        rw [update_ok r lane _ hb]
        simp only [bind_tc_ok, lift]
        exact tail z (by rw [if_pos e7', hzv])
      · have e7' : lane.val ≠ 7 := fun h => e7 (by
          apply UScalar.eq_of_val_eq; rw [h]; simp)
        have h8 : (Usize.wrapping_add 8#usize lane).val = 8 + lane.val := by rw [uadd _ _ (by scalar_tac)]; simp
        rw [if_neg e7]
        simp only [lift, bind_tc_ok]
        rw [index_ok row0 _ (by rw [h8]; simp; omega)]
        simp only [bind_tc_ok]
        rw [update_ok r lane _ hb]
        simp only [bind_tc_ok, lift]
        exact tail _ (by rw [if_neg e7', h8])

theorem rep8 (k : Nat) : (((Array.repeat 8#usize 0#u32 : Array U32 8#usize).val[k]! : U32)) = 0#u32 := by
  rw [Array.repeat_val]
  by_cases hk : k < (8#usize : Usize).val
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_pos hk]; rfl
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_neg hk]; rfl

/-- B3 (b): read-back of a node block written by the copy returns its inputs. -/
theorem read_back_node (prev : Array U32 16#usize) (left right : Array U32 8#usize)
    (hc : ∀ i, i < 8 → (right.val[i]!).val < 2147483647) :
    ∃ pre ab, R0BlockCopies.node_pre right = ok pre ∧ R0BlockCopies.node_absorb left = ok ab ∧
      ∃ c' l' r', R0BlockCopies.read_back prev pre ab = ok (c', l', r') ∧
        ∀ k, k < 8 → c'.val[k]! = prev.val[k]! ∧ l'.val[k]! = left.val[k]! ∧
          (r'.val[k]!).val = (right.val[k]!).val := by
  obtain ⟨pre, hp, hps⟩ := node_pre_spec right hc
  obtain ⟨ab, ha, has⟩ := node_absorb_spec left
  have h15 : (pre.val[15]!).val < 2147483647 := by
    rw [hps]; have := hc 7 (by norm_num); split_ifs <;> omega
  obtain ⟨c', l', r', hok, hs⟩ := read_back_loop_spec prev pre ab h15 8 0#usize
    (Array.repeat 8#usize 0#u32) (Array.repeat 8#usize 0#u32) (Array.repeat 8#usize 0#u32) (by simp)
  refine ⟨pre, ab, hp, ha, c', l', r', by rw [R0BlockCopies.read_back]; exact hok, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hs k
  rw [show (0#usize : Usize).val = 0 by simp] at h1 h2 h3
  have hk' : 0 ≤ k ∧ k < 8 := ⟨Nat.zero_le _, hk⟩
  refine ⟨by rw [h1, if_pos hk'], by rw [h2, if_pos hk', has, if_pos hk], ?_⟩
  rw [h3, if_pos hk']
  by_cases e : k = 7
  · rw [if_pos e, e, hps 15, if_neg (show ¬ (15 < 8) by norm_num), if_pos rfl]
    have hr7 := hc 7 (by norm_num)
    generalize (right.val[7]!).val = x at hr7 ⊢
    split_ifs <;> omega
  · rw [if_neg e, hps, if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show 8 + k - 8 = k by omega]

#print axioms read_back_loop_spec
#print axioms read_back_node
end R0Z.WriterRefine
