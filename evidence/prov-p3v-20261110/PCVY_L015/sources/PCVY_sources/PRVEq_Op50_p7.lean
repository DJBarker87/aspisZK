import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p6
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le)

/-! ## 4. little-endian words -/

theorem fromLE_toNat (l : List U8) :
    (BitVec.fromLEBytes (l.map U8.bv)).toNat = le (l.map bt) := by
  induction l with
  | nil => simp [BitVec.fromLEBytes, le]
  | cons a t ih =>
    have ha : a.val < 256 := by scalar_tac
    have hlt := (BitVec.fromLEBytes (t.map U8.bv)).isLt
    simp only [List.length_map] at hlt
    have hP : 1 ≤ 2 ^ (8 * t.length) := Nat.one_le_two_pow
    have hW : 2 ^ (8 * (t.length + 1)) = 2 ^ (8 * t.length) * 256 := by
      rw [Nat.mul_succ, Nat.pow_add]; norm_num
    simp only [List.map_cons, BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, List.length_map, List.length_cons, hW]
    have h1 : a.bv.toNat % (2 ^ (8 * t.length) * 256) = a.val := by
      rw [UScalar.bv_toNat]; exact Nat.mod_eq_of_lt (by omega)
    have h2 : (BitVec.fromLEBytes (t.map U8.bv)).toNat % (2 ^ (8 * t.length) * 256) =
        (BitVec.fromLEBytes (t.map U8.bv)).toNat := Nat.mod_eq_of_lt (by omega)
    have h3 : ((BitVec.fromLEBytes (t.map U8.bv)).toNat <<< 8) % (2 ^ (8 * t.length) * 256) =
        (BitVec.fromLEBytes (t.map U8.bv)).toNat <<< 8 :=
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
    simp only [h1, h2, h3, ih]
    show _ = (bt a).toNat + 256 * le (t.map bt)
    rw [bt_toNat, or_shl8 _ _ ha]
    omega

theorem u32_val (a : Std.Array U8 4#usize) :
    (core.num.U32.from_le_bytes a).val = le (a.val.map bt) := by
  unfold core.num.U32.from_le_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact fromLE_toNat a.val

theorem u64_val (a : Std.Array U8 8#usize) :
    (core.num.U64.from_le_bytes a).val = le (a.val.map bt) := by
  unfold core.num.U64.from_le_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact fromLE_toNat a.val

/-- generic slice, same shape as the transcription's `sl` on bytes -/
def slg {α : Type} (l : List α) (a c : Nat) : List α := (l.drop a).take (c - a)

theorem sl_map {α : Type} (f : α → UInt8) (l : List α) (a c : Nat) :
    sl (l.map f) a c = (slg l a c).map f := by
  simp [sl, slg, List.map_take, List.map_drop]

theorem sl_eq {α : Type} (l : List α) (s n : Nat) (m : List α) (hm : m.length = n)
    (h : ∀ j, j < n → l[s + j]? = m[j]?) : slg l s (s + n) = m := by
  apply List.ext_getElem?
  intro t
  unfold slg
  rw [Nat.add_sub_cancel_left, List.getElem?_take, List.getElem?_drop]
  by_cases ht : t < n
  · simp only [ht, if_true]
    exact h t ht
  · simp only [ht, if_false]
    exact (List.getElem?_eq_none (by omega)).symm

theorem word32_eq (b : Slice U8) (s : Usize) (h : s.val + 4 ≤ b.val.length) :
    ∃ w : U32, NCV_Reference.word32 b s = ok w ∧
      w.val = le (sl (b.val.map bt) s.val (s.val + 4)) := by
  have hb := b.property
  obtain ⟨s1, e1, v1⟩ := add_ok s 1#usize (by scalar_tac)
  obtain ⟨s2, e2, v2⟩ := add_ok s 2#usize (by scalar_tac)
  obtain ⟨s3, e3, v3⟩ := add_ok s 3#usize (by scalar_tac)
  rw [one_val] at v1
  rw [two_val] at v2
  rw [three_val] at v3
  have h0 : s.val < b.val.length := by omega
  have h1 : s1.val < b.val.length := by omega
  have h2 : s2.val < b.val.length := by omega
  have h3 : s3.val < b.val.length := by omega
  refine ⟨_, ?_, ?_⟩
  · unfold NCV_Reference.word32
    simp only [idx_slice b s h0, e1, e2, e3, idx_slice b s1 h1, idx_slice b s2 h2,
      idx_slice b s3 h3, bind_tc_ok]
    rfl
  · rw [u32_val, sl_map]
    have hs : slg b.val s.val (s.val + 4) =
        [b.val[s.val], b.val[s1.val], b.val[s2.val], b.val[s3.val]] := by
      apply sl_eq _ _ _ _ rfl
      intro j hj
      obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · simp [List.getElem?_eq_getElem h0]
      · rw [Nat.add_comm, ← v1]; simp [List.getElem?_eq_getElem h1]
      · rw [Nat.add_comm, ← v2]; simp [List.getElem?_eq_getElem h2]
      · rw [Nat.add_comm, ← v3]; simp [List.getElem?_eq_getElem h3]
    rw [hs]
    rfl

theorem word64_eq (b : Slice U8) (s : Usize) (h : s.val + 8 ≤ b.val.length) :
    ∃ w : U64, NCV_Reference.word64 b s = ok w ∧
      w.val = le (sl (b.val.map bt) s.val (s.val + 8)) := by
  have hb := b.property
  obtain ⟨s1, e1, v1⟩ := add_ok s 1#usize (by scalar_tac)
  obtain ⟨s2, e2, v2⟩ := add_ok s 2#usize (by scalar_tac)
  obtain ⟨s3, e3, v3⟩ := add_ok s 3#usize (by scalar_tac)
  obtain ⟨s4, e4, v4⟩ := add_ok s 4#usize (by scalar_tac)
  obtain ⟨s5, e5, v5⟩ := add_ok s 5#usize (by scalar_tac)
  obtain ⟨s6, e6, v6⟩ := add_ok s 6#usize (by scalar_tac)
  obtain ⟨s7, e7, v7⟩ := add_ok s 7#usize (by scalar_tac)
  rw [one_val] at v1
  rw [two_val] at v2
  rw [three_val] at v3
  rw [four_val] at v4
  rw [five_val] at v5
  rw [six_val] at v6
  rw [seven_val] at v7
  have h0 : s.val < b.val.length := by omega
  have h1 : s1.val < b.val.length := by omega
  have h2 : s2.val < b.val.length := by omega
  have h3 : s3.val < b.val.length := by omega
  have h4 : s4.val < b.val.length := by omega
  have h5 : s5.val < b.val.length := by omega
  have h6 : s6.val < b.val.length := by omega
  have h7 : s7.val < b.val.length := by omega
  refine ⟨_, ?_, ?_⟩
  · unfold NCV_Reference.word64
    simp only [idx_slice b s h0, e1, e2, e3, e4, e5, e6, e7, idx_slice b s1 h1,
      idx_slice b s2 h2, idx_slice b s3 h3, idx_slice b s4 h4, idx_slice b s5 h5,
      idx_slice b s6 h6, idx_slice b s7 h7, bind_tc_ok]
    rfl
  · rw [u64_val, sl_map]
    have hs : slg b.val s.val (s.val + 8) =
        [b.val[s.val], b.val[s1.val], b.val[s2.val], b.val[s3.val],
         b.val[s4.val], b.val[s5.val], b.val[s6.val], b.val[s7.val]] := by
      apply sl_eq _ _ _ _ rfl
      intro j hj
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      · simp [List.getElem?_eq_getElem h0]
      · rw [Nat.add_comm, ← v1]; simp [List.getElem?_eq_getElem h1]
      · rw [Nat.add_comm, ← v2]; simp [List.getElem?_eq_getElem h2]
      · rw [Nat.add_comm, ← v3]; simp [List.getElem?_eq_getElem h3]
      · rw [Nat.add_comm, ← v4]; simp [List.getElem?_eq_getElem h4]
      · rw [Nat.add_comm, ← v5]; simp [List.getElem?_eq_getElem h5]
      · rw [Nat.add_comm, ← v6]; simp [List.getElem?_eq_getElem h6]
      · rw [Nat.add_comm, ← v7]; simp [List.getElem?_eq_getElem h7]
    rw [hs]
    rfl

#print axioms or_shl8
#print axioms fromLE_toNat
#print axioms u32_val
#print axioms u64_val
#print axioms word32_eq
#print axioms word64_eq

/-! ## 5. eq_digest_loop / eq_digest -/

theorem idx_dig (a : Std.Array U32 8#usize) (i : Usize) (h : i.val < a.val.length) :
    a.index_usize i = ok (a.val[i.val]'h) := by
  obtain ⟨x, hx, hv⟩ := WP.spec_imp_exists (Array.index_usize_spec a i h)
  rw [hx, hv]

theorem lt8 (i : Usize) (h : i.val < 8) : i < 8#usize := by scalar_tac
theorem not_lt8 (i : Usize) (h : ¬ i.val < 8) : ¬ (i < 8#usize) := by scalar_tac

theorem dlen (a : Std.Array U32 8#usize) : a.val.length = 8 := by
  have := a.property; simpa using this

theorem eqd_body_end (a b : Std.Array U32 8#usize) (i : Usize) (h : ¬ i.val < 8) :
    NCV_Reference.eq_digest_loop.body a b i = ok (done none) := by
  have hge := not_lt8 i h
  unfold NCV_Reference.eq_digest_loop.body
  simp only [hge, if_false]

theorem eqd_body_diff (a b : Std.Array U32 8#usize) (i : Usize) (hi : i.val < 8)
    (hia : i.val < a.val.length) (hib : i.val < b.val.length)
    (hne : a.val[i.val]'hia ≠ b.val[i.val]'hib) :
    NCV_Reference.eq_digest_loop.body a b i = ok (done (some false)) := by
  have hlt := lt8 i hi
  have hb' : (a.val[i.val]'hia != b.val[i.val]'hib) = true := by simp [hne]
  unfold NCV_Reference.eq_digest_loop.body
  simp only [hlt, if_true, bind_tc_ok, idx_dig a i hia, idx_dig b i hib, hb']

theorem eqd_body_same (a b : Std.Array U32 8#usize) (i c : Usize) (hi : i.val < 8)
    (hia : i.val < a.val.length) (hib : i.val < b.val.length)
    (hne : a.val[i.val]'hia = b.val[i.val]'hib)
    (hc : (i + 1#usize : Result Usize) = ok c) :
    NCV_Reference.eq_digest_loop.body a b i = ok (cont c) := by
  have hlt := lt8 i hi
  have hb' : (a.val[i.val]'hia != b.val[i.val]'hib) = false := by simp [hne]
  unfold NCV_Reference.eq_digest_loop.body
  simp only [hlt, if_true, bind_tc_ok, idx_dig a i hia, idx_dig b i hib, hb', Bool.false_eq_true,
    if_false, hc]

theorem eq_digest_loop_eq (a b : Std.Array U32 8#usize) :
    ∀ (k : Nat) (i : Usize), 8 - i.val = k → i.val ≤ 8 →
    NCV_Reference.eq_digest_loop a b i =
      ok (if a.val.drop i.val = b.val.drop i.val then none else some false) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    have e1 : a.val.drop i.val = [] := List.drop_eq_nil_of_le (by rw [dlen]; omega)
    have e2 : b.val.drop i.val = [] := List.drop_eq_nil_of_le (by rw [dlen]; omega)
    unfold NCV_Reference.eq_digest_loop
    rw [loop.eq_def]
    simp only [eqd_body_end a b i (by omega), e1, e2]
    simp
  | succ k ih =>
    intro i hk hi
    have hi8 : i.val < 8 := by omega
    have hia : i.val < a.val.length := by rw [dlen]; exact hi8
    have hib : i.val < b.val.length := by rw [dlen]; exact hi8
    obtain ⟨c, hc, hcv⟩ := add_ok i 1#usize (by scalar_tac)
    have hcv' : c.val = i.val + 1 := by rw [hcv, one_val]
    have ea : a.val.drop i.val = a.val[i.val]'hia :: a.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hia
    have eb : b.val.drop i.val = b.val[i.val]'hib :: b.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hib
    have ih' := ih c (by omega) (by omega)
    rw [hcv'] at ih'
    unfold NCV_Reference.eq_digest_loop
    rw [loop.eq_def]
    by_cases hne : a.val[i.val]'hia = b.val[i.val]'hib
    · simp only [eqd_body_same a b i c hi8 hia hib hne hc]
      unfold NCV_Reference.eq_digest_loop at ih'
      have key : (a.val.drop i.val = b.val.drop i.val) ↔
          (a.val.drop (i.val + 1) = b.val.drop (i.val + 1)) := by
        rw [ea, eb, hne]; simp only [List.cons.injEq, true_and]
      rw [ih']
      simp only [key]
    · simp only [eqd_body_diff a b i hi8 hia hib hne]
      have key : ¬ (a.val.drop i.val = b.val.drop i.val) := by
        rw [ea, eb]; simp only [List.cons.injEq, not_and]; intro h; exact absurd h hne
      simp only [key, if_false]

theorem eq_digest_eq (a b : Std.Array U32 8#usize) :
    NCV_Reference.eq_digest a b = ok (decide (a.val = b.val)) := by
  unfold NCV_Reference.eq_digest
  rw [eq_digest_loop_eq a b 8 (0#usize) (by simp) (by simp)]
  by_cases he : a.val = b.val
  · simp [he]
  · have : ¬ a.val.drop 0 = b.val.drop 0 := by simpa using he
    simp [this, he]

#print axioms eq_digest_loop_eq
#print axioms eq_digest_eq
end PCVY_Op50
