import R0Z.WriterRefineValueBlock
import R0Z.WriterRefineOccRow
import R0Z.BuilderModelCopyMisc

/-! The extracted value-aux writer computes the model's value rows
(DESIGN-BUILDER-MODEL §9): `write_value_block values` returns `ok b` and every
lifted cell of block 63 outside the occupancy rows 9 and 10 equals the model's
`auxCell C (1008 + r) c`, for a characteristic-(2^31−1) field and values below
2^30 equal to the model's `C.values`; rows 9 and 10 are zero. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

theorem m31_sub_spec (a b : U32) (ha : a.val < 2 ^ 30) (hb : b.val < 2 ^ 30) :
    ∃ z, m31_sub a b = ok z ∧ z.val = (if b.val ≤ a.val then a.val - b.val else a.val + 2147483647 - b.val) := by
  have hP : (P : U32).val = 2147483647 := by rw [P]; simp
  have h1 : (U32.wrapping_add a P).val = a.val + 2147483647 := by
    rw [U32.wrapping_add_val_eq, hP]; exact Nat.mod_eq_of_lt (by rw [UScalar.size_def]; simp; omega)
  have h2 : (U32.wrapping_sub (U32.wrapping_add a P) b).val = a.val + 2147483647 - b.val := by
    rw [U32.wrapping_sub_val_eq, h1, UScalar.size_def]
    simp only [show UScalarTy.U32.numBits = 32 from rfl]
    rw [show a.val + 2147483647 + (2 ^ 32 - b.val) = (a.val + 2147483647 - b.val) + 2 ^ 32 by omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [m31_sub]
  simp only [lift, bind_tc_ok]
  by_cases hs : U32.wrapping_sub (U32.wrapping_add a P) b >= P
  · rw [if_pos hs]
    have hs' : 2147483647 ≤ a.val + 2147483647 - b.val := by
      rw [ge_iff_le, UScalar.le_equiv, hP, h2] at hs; exact hs
    refine ⟨_, rfl, ?_⟩
    rw [U32.wrapping_sub_val_eq, h2, hP, UScalar.size_def]
    simp only [show UScalarTy.U32.numBits = 32 from rfl]
    rw [if_pos (by omega)]
    rw [show a.val + 2147483647 - b.val + (2 ^ 32 - 2147483647) = (a.val - b.val) + 2 ^ 32 by omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg hs]
    have hs' : ¬ 2147483647 ≤ a.val + 2147483647 - b.val := by
      rw [ge_iff_le, UScalar.le_equiv, hP, h2] at hs; exact hs
    exact ⟨_, rfl, by rw [h2, if_neg (by omega)]⟩

/-- The cells of the value block (rows 6 and 7 hold the conservation cells). -/
def FinalVal (vals : Nat → Nat) (k : Nat) : Nat :=
  if k = 96 then vals 0 else if k = 97 then vals 1
  else if k = 98 ∨ k = 112 then (if vals 1 ≤ vals 0 then vals 0 - vals 1 else vals 0 + 2147483647 - vals 1)
  else if k = 113 then vals 2 else OuterVal vals 0 (fun _ => 0) k

theorem value_block (values : Array U32 3#usize) (hv : ∀ i, i < 3 → (values.val[i]!).val < 2 ^ 30) :
    ∃ b, write_value_block values = ok b ∧
      ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k := by
  obtain ⟨b1, hb1, hs1⟩ := value_outer values 3 0#usize (Array.repeat 256#usize 0#u32) (by simp)
  have h0 : (0#usize : Usize).val < (3#usize).val := by simp
  have h1 : (1#usize : Usize).val < (3#usize).val := by simp
  have h2 : (2#usize : Usize).val < (3#usize).val := by simp
  obtain ⟨z, hz, hzv⟩ := m31_sub_spec (values.val[(0#usize : Usize).val]!) (values.val[(1#usize : Usize).val]!)
    (hv 0 (by simp)) (hv 1 (by simp))
  have e96 : (Usize.wrapping_mul 6#usize 16#usize).val = 96 := by rw [umul _ _ (by simp)]; simp
  have e97 : (Usize.wrapping_add (Usize.wrapping_mul 6#usize 16#usize) 1#usize).val = 97 := by
    rw [uadd _ _ (by rw [e96]; simp), e96]; simp
  have e98 : (Usize.wrapping_add (Usize.wrapping_mul 6#usize 16#usize) 2#usize).val = 98 := by
    rw [uadd _ _ (by rw [e96]; simp), e96]; simp
  have e112 : (Usize.wrapping_mul 7#usize 16#usize).val = 112 := by rw [umul _ _ (by simp)]; simp
  have e113 : (Usize.wrapping_add (Usize.wrapping_mul 7#usize 16#usize) 1#usize).val = 113 := by
    rw [uadd _ _ (by rw [e112]; simp), e112]; simp
  have lt : ∀ (i : Usize) (n : Nat), i.val = n → n < 256 → i.val < (256#usize).val := by
    intro i n h hn; rw [h]; simpa using hn
  let v0 := values.val[(0#usize : Usize).val]!
  let v1 := values.val[(1#usize : Usize).val]!
  let v2 := values.val[(2#usize : Usize).val]!
  let c1 := b1.set (Usize.wrapping_mul 6#usize 16#usize) v0
  let c2 := c1.set (Usize.wrapping_add (Usize.wrapping_mul 6#usize 16#usize) 1#usize) v1
  let c3 := c2.set (Usize.wrapping_add (Usize.wrapping_mul 6#usize 16#usize) 2#usize) z
  let c4 := c3.set (Usize.wrapping_mul 7#usize 16#usize) z
  let c5 := c4.set (Usize.wrapping_add (Usize.wrapping_mul 7#usize 16#usize) 1#usize) v2
  refine ⟨c5, ?_, fun k => ?_⟩
  · rw [write_value_block]
    simp only [bind_tc_ok, lift]
    rw [hb1]
    simp only [bind_tc_ok]
    rw [index_ok values _ h0, index_ok values _ h1]
    simp only [bind_tc_ok]
    rw [hz]
    simp only [bind_tc_ok]
    rw [update_ok _ _ _ (lt _ _ e96 (by omega))]
    simp only [bind_tc_ok]
    rw [update_ok _ _ _ (lt _ _ e97 (by omega))]
    simp only [bind_tc_ok]
    rw [update_ok _ _ _ (lt _ _ e98 (by omega))]
    simp only [bind_tc_ok]
    rw [update_ok _ _ _ (lt _ _ e112 (by omega))]
    simp only [bind_tc_ok]
    rw [index_ok values _ h2]
    simp only [bind_tc_ok]
    rw [update_ok _ _ _ (lt _ _ e113 (by omega))]
  · show (c5.val[k]!).val = _
    rw [set_get' c4 _ _ (lt _ _ e113 (by omega)), e113, set_get' c3 _ _ (lt _ _ e112 (by omega)), e112,
      set_get' c2 _ _ (lt _ _ e98 (by omega)), e98, set_get' c1 _ _ (lt _ _ e97 (by omega)), e97,
      set_get' b1 _ _ (lt _ _ e96 (by omega)), e96]
    unfold FinalVal
    have hrep : ∀ k : Nat, (((Array.repeat 256#usize 0#u32 : Array U32 256#usize).val[k]! : U32)).val = 0 := by
      intro k
      rw [Array.repeat_val]
      by_cases hk : k < (256#usize : Usize).val
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_pos hk]; rfl
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_neg hk]; rfl
    by_cases a113 : k = 113
    · rw [if_pos a113, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos a113]
      try simp [v0, v1, v2]
    rw [if_neg a113]
    by_cases a112 : k = 112
    · rw [if_pos a112, if_neg (by omega), if_neg (by omega), if_pos (Or.inr a112), hzv]
      try simp [v0, v1, v2]
    rw [if_neg a112]
    by_cases a98 : k = 98
    · rw [if_pos a98, if_neg (by omega), if_neg (by omega), if_pos (Or.inl a98), hzv]
      try simp [v0, v1, v2]
    rw [if_neg a98]
    by_cases a97 : k = 97
    · rw [if_pos a97, if_neg (by omega), if_pos a97]
      try simp [v0, v1, v2]
    rw [if_neg a97]
    by_cases a96 : k = 96
    · rw [if_pos a96, if_pos a96]
      try simp [v0, v1, v2]
    rw [if_neg a96, if_neg a96, if_neg a97, if_neg (by omega), if_neg a113, hs1 k]
    simp only [show (0#usize : Usize).val = 0 by simp, hrep]

/-! ### Against the model's aux rows -/

variable {K : Type} [Field K]

theorem tOf_rc (b r c : Nat) (hc : c < 16) :
    tOf b (r * 16 + c) = if r = b then c else if r = b + 1 then 10 + c else 20 + c := by
  unfold tOf
  rw [show (r * 16 + c) / 16 = r by omega, show (r * 16 + c) % 16 = c by omega]

theorem ov_rc (vals : Nat → Nat) (r c : Nat) (hc : c < 16) :
    OuterVal vals 0 (fun _ => 0) (r * 16 + c) =
      if jOf r < 3 then (if c < 10 then vals (jOf r) / 2 ^ tOf (2 * jOf r) (r * 16 + c) % 2
        else if c = 10 ∧ r = 2 * jOf r then vals (jOf r) else 0) else 0 := by
  unfold OuterVal
  rw [show (r * 16 + c) / 16 = r by omega, show (r * 16 + c) % 16 = c by omega]
  by_cases h : jOf r < 3
  · rw [if_pos ⟨h, Nat.zero_le _⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/-- The model rows the value writer fills, and their premises. -/
structure ValueLifts (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K) : Prop where
  small : ∀ i, i < 3 → (values.val[i]!).val < 2 ^ 30
  eq : ∀ i : Fin 3, C.values i = (values.val[i.val]!).val

theorem liftU_nat (x : U32) (n : Nat) (h : x.val = n) : liftU (K := K) x = (n : K) := by
  unfold liftU; rw [h]

theorem m31_lift_sub [CharP K 0x7fffffff] (a b : Nat) (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) :
    (((if b ≤ a then a - b else a + 2147483647 - b : Nat)) : K) = (a : K) - (b : K) := by
  split_ifs with h
  · rw [Nat.cast_sub h]
  · rw [Nat.cast_sub (by omega), Nat.cast_add, CharP.cast_eq_zero K 0x7fffffff]
    ring

theorem value_rows_zero (values : Array U32 3#usize) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (r : Nat) (hr : r = 9 ∨ r = 10)
    (c : Nat) (hc : c < 16) : (b.val[r * 16 + c]!).val = 0 := by
  rw [hb]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc]
  rcases hr with rfl | rfl
  · rw [show jOf 9 = 3 by decide, if_neg (by norm_num)]
  · rw [show jOf 10 = 3 by decide, if_neg (by norm_num)]

theorem value_row_0 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[0 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 0) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 0 = 0 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 0 : Nat) = 1008 by norm_num, R0Z.BuilderModel.aux_1008]
  unfold R0Z.BuilderModel.valueBaseCell
  rw [hl.eq 0]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_pos (by norm_num)]; rfl
  · rw [if_neg c10, if_neg c10]
    by_cases e : c.val = 10
    · rw [if_pos ⟨e, by norm_num⟩, if_pos e]; rfl
    · rw [if_neg (fun h => e h.1), if_neg e]; simp

theorem value_row_1 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[1 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 1) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 1 = 0 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 1 : Nat) = 1009 by norm_num, R0Z.BuilderModel.aux_1009]
  unfold R0Z.BuilderModel.valueMidCell
  rw [hl.eq 0]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_neg (by norm_num), if_pos (by norm_num), R0Z.BuilderModel.bitK_mid]; rfl
  · rw [if_neg c10, if_neg c10, if_neg (fun h => by omega)]; simp

theorem value_row_2 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[2 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 2) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 2 = 1 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 2 : Nat) = 1010 by norm_num, R0Z.BuilderModel.aux_1010]
  unfold R0Z.BuilderModel.valueBaseCell
  rw [hl.eq 1]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_pos (by norm_num)]; rfl
  · rw [if_neg c10, if_neg c10]
    by_cases e : c.val = 10
    · rw [if_pos ⟨e, by norm_num⟩, if_pos e]; rfl
    · rw [if_neg (fun h => e h.1), if_neg e]; simp

theorem value_row_3 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[3 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 3) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 3 = 1 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 3 : Nat) = 1011 by norm_num, R0Z.BuilderModel.aux_1011]
  unfold R0Z.BuilderModel.valueMidCell
  rw [hl.eq 1]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_neg (by norm_num), if_pos (by norm_num), R0Z.BuilderModel.bitK_mid]; rfl
  · rw [if_neg c10, if_neg c10, if_neg (fun h => by omega)]; simp

theorem value_row_4 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[4 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 4) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 4 = 2 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 4 : Nat) = 1012 by norm_num, R0Z.BuilderModel.aux_1012]
  unfold R0Z.BuilderModel.valueBaseCell
  rw [hl.eq 2]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_pos (by norm_num)]; rfl
  · rw [if_neg c10, if_neg c10]
    by_cases e : c.val = 10
    · rw [if_pos ⟨e, by norm_num⟩, if_pos e]; rfl
    · rw [if_neg (fun h => e h.1), if_neg e]; simp

theorem value_row_5 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[5 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 5) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 5 = 2 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 5 : Nat) = 1013 by norm_num, R0Z.BuilderModel.aux_1013]
  unfold R0Z.BuilderModel.valueMidCell
  rw [hl.eq 2]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_neg (by norm_num), if_pos (by norm_num), R0Z.BuilderModel.bitK_mid]; rfl
  · rw [if_neg c10, if_neg c10, if_neg (fun h => by omega)]; simp

theorem value_row_6 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[6 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 6) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [show (1008 + 6 : Nat) = 1014 by norm_num, R0Z.BuilderModel.aux_1014, hl.eq 0, hl.eq 1]
  have s0 := hl.small 0 (by norm_num)
  have s1 := hl.small 1 (by norm_num)
  by_cases e0 : c.val = 0
  · rw [if_pos (by omega), if_pos e0]; rfl
  rw [if_neg (by omega), if_neg e0]
  by_cases e1 : c.val = 1
  · rw [if_pos (by omega), if_pos e1]; rfl
  rw [if_neg (by omega), if_neg e1]
  by_cases e2 : c.val = 2
  · rw [if_pos (Or.inl (by omega)), if_pos e2]
    exact m31_lift_sub _ _ s0 s1
  rw [if_neg (by omega), if_neg (by omega), if_neg e2, ov_rc _ _ _ hc, show jOf 6 = 3 by decide,
    if_neg (by norm_num)]
  simp

theorem value_row_7 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[7 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 7) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [show (1008 + 7 : Nat) = 1015 by norm_num, R0Z.BuilderModel.aux_1015, hl.eq 0, hl.eq 1, hl.eq 2]
  have s0 := hl.small 0 (by norm_num)
  have s1 := hl.small 1 (by norm_num)
  by_cases e0 : c.val = 0
  · rw [if_neg (by omega), if_neg (by omega), if_pos (Or.inr (by omega)), if_pos e0]
    exact m31_lift_sub _ _ s0 s1
  rw [if_neg e0]
  by_cases e1 : c.val = 1
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos e1]; rfl
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg e1, ov_rc _ _ _ hc,
    show jOf 7 = 3 by decide, if_neg (by norm_num)]
  simp

theorem value_row_8 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[8 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 8) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 8 = 2 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 8 : Nat) = 1016 by norm_num, R0Z.BuilderModel.aux_1016]
  unfold R0Z.BuilderModel.valueHiCell
  rw [hl.eq 2]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_neg (by norm_num), if_neg (by norm_num), R0Z.BuilderModel.bitK_hi]; rfl
  · rw [if_neg c10, if_neg c10, if_neg (fun h => by omega)]; simp

theorem value_row_11 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[11 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 11) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 11 = 3 by decide, if_neg (by norm_num)]
  rw [show (1008 + 11 : Nat) = 1019 by norm_num, show R0Z.BuilderModel.auxCell C 1019 c = 0 by
    simp [R0Z.BuilderModel.auxCell]]
  simp

theorem value_row_12 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[12 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 12) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 12 = 0 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 12 : Nat) = 1020 by norm_num, R0Z.BuilderModel.aux_1020]
  unfold R0Z.BuilderModel.valueHiCell
  rw [hl.eq 0]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_neg (by norm_num), if_neg (by norm_num), R0Z.BuilderModel.bitK_hi]; rfl
  · rw [if_neg c10, if_neg c10, if_neg (fun h => by omega)]; simp

theorem value_row_13 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[13 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 13) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 13 = 3 by decide, if_neg (by norm_num)]
  rw [show (1008 + 13 : Nat) = 1021 by norm_num, show R0Z.BuilderModel.auxCell C 1021 c = 0 by
    simp [R0Z.BuilderModel.auxCell]]
  simp

theorem value_row_14 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[14 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 14) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 14 = 1 by decide, if_pos (by norm_num), tOf_rc _ _ _ hc]
  rw [show (1008 + 14 : Nat) = 1022 by norm_num, R0Z.BuilderModel.aux_1022]
  unfold R0Z.BuilderModel.valueHiCell
  rw [hl.eq 1]
  by_cases c10 : c.val < 10
  · rw [if_pos c10, if_pos c10, if_neg (by norm_num), if_neg (by norm_num), R0Z.BuilderModel.bitK_hi]; rfl
  · rw [if_neg c10, if_neg c10, if_neg (fun h => by omega)]; simp

theorem value_row_15 [CharP K 0x7fffffff] (values : Array U32 3#usize) (C : R0Z.BuilderModel.Cells K)
    (hl : ValueLifts values C) (b : Array U32 256#usize)
    (hb : ∀ k, (b.val[k]!).val = FinalVal (fun i => (values.val[i]!).val) k) (c : Fin 16) :
    liftU (K := K) (b.val[15 * 16 + c.val]!) = R0Z.BuilderModel.auxCell C (1008 + 15) c := by
  have hc := c.isLt
  rw [liftU_nat _ _ (hb _)]
  unfold FinalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), ov_rc _ _ _ hc,
    show jOf 15 = 3 by decide, if_neg (by norm_num)]
  rw [show (1008 + 15 : Nat) = 1023 by norm_num, show R0Z.BuilderModel.auxCell C 1023 c = 0 by
    simp [R0Z.BuilderModel.auxCell]]
  simp

#print axioms m31_sub_spec
#print axioms value_block
#print axioms m31_lift_sub
#print axioms value_rows_zero
#print axioms value_row_0
#print axioms value_row_1
#print axioms value_row_2
#print axioms value_row_3
#print axioms value_row_4
#print axioms value_row_5
#print axioms value_row_6
#print axioms value_row_7
#print axioms value_row_8
#print axioms value_row_11
#print axioms value_row_12
#print axioms value_row_13
#print axioms value_row_14
#print axioms value_row_15
end R0Z.WriterRefine
