import R0Z.WriterRefineOcc

/-! The extracted forest path-aux writer (DESIGN-BUILDER-MODEL §9):
`write_path_level` (copy of pair_forest_trace.rs:142-159) writes exactly the
base row (bit, current) and the successor row (left, right) of its level. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

theorem set_get' {n : Usize} (v : Array U32 n) (i : Usize) (x : U32) (hi : i.val < n.val) (k : Nat) :
    (v.set i x).val[k]! = if k = i.val then x else v.val[k]! := by
  rw [Array.set_val_eq]
  exact getElem!_set_list _ _ _ _ (by rw [v.property]; exact hi)

theorem path_loop (cur l r : Array U32 8#usize) (base : Usize) (hb : base.val + 32 ≤ 1536) :
    ∀ (n : Nat) (lane : Usize) (buf : Array U32 1536#usize), lane.val + n = 8 →
      ∃ b', write_path_level_loop cur l r buf base lane = ok b' ∧
        ∀ k, b'.val[k]! =
          if base.val + 1 + lane.val ≤ k ∧ k < base.val + 9 then cur.val[k - base.val - 1]!
          else if base.val + 16 + lane.val ≤ k ∧ k < base.val + 24 then l.val[k - base.val - 16]!
          else if base.val + 24 + lane.val ≤ k ∧ k < base.val + 32 then r.val[k - base.val - 24]!
          else buf.val[k]!
  | 0, lane, buf, h => by
      refine ⟨buf, ?_, fun k => ?_⟩
      · rw [write_path_level_loop]
        rw [if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  | n + 1, lane, buf, h => by
      have hlt : lane < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hl8 : lane.val < 8 := by omega
      have e1 : (Usize.wrapping_add base 1#usize).val = base.val + 1 := uadd _ _ (by scalar_tac)
      have i2 : (Usize.wrapping_add (Usize.wrapping_add base 1#usize) lane).val =
          base.val + 1 + lane.val := by rw [uadd _ _ (by scalar_tac), e1]
      have e16 : (Usize.wrapping_add base 16#usize).val = base.val + 16 := uadd _ _ (by scalar_tac)
      have i5 : (Usize.wrapping_add (Usize.wrapping_add base 16#usize) lane).val =
          base.val + 16 + lane.val := by rw [uadd _ _ (by scalar_tac), e16]
      have e24 : (Usize.wrapping_add (Usize.wrapping_add base 16#usize) 8#usize).val =
          base.val + 24 := by rw [uadd _ _ (by scalar_tac), e16]; simp
      have i9 : (Usize.wrapping_add (Usize.wrapping_add (Usize.wrapping_add base 16#usize) 8#usize)
          lane).val = base.val + 24 + lane.val := by rw [uadd _ _ (by scalar_tac), e24]
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      let b1 := buf.set (Usize.wrapping_add (Usize.wrapping_add base 1#usize) lane) (cur.val[lane.val]!)
      let b2 := b1.set (Usize.wrapping_add (Usize.wrapping_add base 16#usize) lane) (l.val[lane.val]!)
      let b3 := b2.set (Usize.wrapping_add (Usize.wrapping_add (Usize.wrapping_add base 16#usize)
        8#usize) lane) (r.val[lane.val]!)
      obtain ⟨b', hb', hspec⟩ := path_loop cur l r base hb n (Usize.wrapping_add lane 1#usize) b3
        (by rw [hl1]; omega)
      refine ⟨b', ?_, fun k => ?_⟩
      · rw [write_path_level_loop, if_pos hlt]
        have hl8' : lane.val < (8#usize).val := by simpa using hl8
        rw [index_ok cur lane hl8']
        simp only [lift, bind_tc_ok]
        rw [update_ok buf _ _ (show _ < (1536#usize).val by rw [i2]; simpa using (by omega : base.val + 1 + lane.val < 1536))]
        simp only [bind_tc_ok]
        rw [index_ok l lane hl8']
        simp only [bind_tc_ok]
        rw [update_ok b1 _ _ (show _ < (1536#usize).val by rw [i5]; simpa using (by omega : base.val + 16 + lane.val < 1536))]
        simp only [bind_tc_ok]
        rw [index_ok r lane hl8']
        simp only [bind_tc_ok]
        rw [update_ok b2 _ _ (show _ < (1536#usize).val by rw [i9]; simpa using (by omega : base.val + 24 + lane.val < 1536))]
        simp only [bind_tc_ok]
        exact hb'
      · rw [hspec k, hl1]
        show _ = _
        have g3 := set_get' b2 _ (r.val[lane.val]!) (show _ < (1536#usize).val by
          rw [i9]; simpa using (by omega : base.val + 24 + lane.val < 1536)) k
        have g2 := set_get' b1 _ (l.val[lane.val]!) (show _ < (1536#usize).val by
          rw [i5]; simpa using (by omega : base.val + 16 + lane.val < 1536)) k
        have g1 := set_get' buf _ (cur.val[lane.val]!) (show _ < (1536#usize).val by
          rw [i2]; simpa using (by omega : base.val + 1 + lane.val < 1536)) k
        rw [i9] at g3; rw [i5] at g2; rw [i2] at g1
        show _ = (if base.val + 1 + lane.val ≤ k ∧ k < base.val + 9 then cur.val[k - base.val - 1]!
          else if base.val + 16 + lane.val ≤ k ∧ k < base.val + 24 then l.val[k - base.val - 16]!
          else if base.val + 24 + lane.val ≤ k ∧ k < base.val + 32 then r.val[k - base.val - 24]!
          else buf.val[k]!)
        by_cases c1 : k = base.val + 1 + lane.val
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), g3, if_neg (by omega), g2,
            if_neg (by omega), g1, if_pos c1, if_pos (by omega)]
          congr 2; omega
        by_cases c2 : k = base.val + 16 + lane.val
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), g3, if_neg (by omega), g2,
            if_pos c2, if_neg (by omega), if_pos (by omega)]
          congr 2; omega
        by_cases c3 : k = base.val + 24 + lane.val
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), g3, if_pos c3,
            if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          congr 2; omega
        rw [g3, if_neg c3, g2, if_neg c2, g1, if_neg c1]
        by_cases d1 : base.val + 1 + (lane.val + 1) ≤ k ∧ k < base.val + 9
        · rw [if_pos d1, if_pos (by omega)]
        rw [if_neg d1]
        by_cases d2 : base.val + 16 + (lane.val + 1) ≤ k ∧ k < base.val + 24
        · rw [if_pos d2, if_neg (by omega), if_pos (by omega)]
        rw [if_neg d2]
        by_cases d3 : base.val + 24 + (lane.val + 1) ≤ k ∧ k < base.val + 32
        · rw [if_pos d3, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        rw [if_neg d3, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem path_base_row_val (level : Usize) (hl : level.val < 24) :
    ∃ z, path_base_local_row level = ok z ∧ z.val = 16 * (level.val / 4) + 1 + 4 * (level.val % 4) := by
  obtain ⟨q, hq, hqv⟩ := UScalar.div_spec level (y := 4#usize) (by simp)
  obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (UScalar.rem_spec level (y := 4#usize) (by simp))
  have hqv' : q.val = level.val / 4 := by rw [hqv]; simp
  have hmv' : m.val = level.val % 4 := by rw [hmv]; simp
  rw [path_base_local_row]
  rw [show level / 4#usize = ok q from hq]
  simp only [bind_tc_ok, lift]
  rw [show level % 4#usize = ok m from hm]
  simp only [bind_tc_ok]
  refine ⟨_, rfl, ?_⟩
  have a1 : (Usize.wrapping_mul 16#usize q).val = 16 * (level.val / 4) := by
    rw [umul _ _ (by simp; omega)]; simp [hqv']
  have a2 : (Usize.wrapping_add (Usize.wrapping_mul 16#usize q) 1#usize).val = 16 * (level.val / 4) + 1 := by
    rw [uadd _ _ (by rw [a1]; simp; omega), a1]; simp
  have a3 : (Usize.wrapping_mul 4#usize m).val = 4 * (level.val % 4) := by
    rw [umul _ _ (by simp; omega)]; simp [hmv']
  rw [uadd _ _ (by rw [a2, a3]; omega), a2, a3]

/-- Exact effect of write_path_level on the 1536-cell path block. -/
theorem path_level (buf : Array U32 1536#usize) (level : Usize) (hl : level.val < 24) (bit : U32)
    (cur l r : Array U32 8#usize) :
    ∃ b', write_path_level buf level bit cur l r = ok b' ∧
      ∀ k, b'.val[k]! =
        let base := (16 * (level.val / 4) + 1 + 4 * (level.val % 4)) * 16
        if k = base then bit
        else if base + 1 ≤ k ∧ k < base + 9 then cur.val[k - base - 1]!
        else if base + 16 ≤ k ∧ k < base + 24 then l.val[k - base - 16]!
        else if base + 24 ≤ k ∧ k < base + 32 then r.val[k - base - 24]!
        else buf.val[k]! := by
  obtain ⟨z, hz, hzv⟩ := path_base_row_val level hl
  have hb : (Usize.wrapping_mul z 16#usize).val = (16 * (level.val / 4) + 1 + 4 * (level.val % 4)) * 16 := by
    rw [umul _ _ (by rw [hzv]; simp; omega), hzv]; simp
  have hbound : (Usize.wrapping_mul z 16#usize).val + 32 ≤ 1536 := by rw [hb]; omega
  obtain ⟨b', hb', hs⟩ := path_loop cur l r (Usize.wrapping_mul z 16#usize) hbound 8 0#usize
    (buf.set (Usize.wrapping_mul z 16#usize) bit) (by simp)
  refine ⟨b', ?_, fun k => ?_⟩
  · rw [write_path_level, hz]
    simp only [bind_tc_ok, lift]
    rw [update_ok buf _ _ (show _ < (1536#usize).val by rw [hb]; simp; omega)]
    simp only [bind_tc_ok]
    exact hb'
  · rw [hs k, set_get' _ _ _ (show _ < (1536#usize).val by rw [hb]; simp; omega) k, hb]
    simp only [show (0#usize : Usize).val = 0 by simp, Nat.add_zero]
    by_cases e : k = (16 * (level.val / 4) + 1 + 4 * (level.val % 4)) * 16
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e, if_pos e]
    · simp only [show (k = (16 * (level.val / 4) + 1 + 4 * (level.val % 4)) * 16) = False from
        propext ⟨e, False.elim⟩, if_false]

#print axioms set_get'
#print axioms path_loop
#print axioms path_base_row_val
#print axioms path_level
end R0Z.WriterRefine
