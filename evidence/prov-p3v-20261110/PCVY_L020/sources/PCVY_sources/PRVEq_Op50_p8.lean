import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p7
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le)

/-! ## 6. digest: instance of the transcription's `decodeDigest` and the digest loop -/

def bytesOf (b : Slice U8) : List UInt8 := b.val.map bt

/-- M31 value of a u32 -/
def u32 (n : Nat) : U32 := ⟨BitVec.ofNat 32 n⟩

theorem u32_val' (n : Nat) (h : n < 2 ^ 32) : (u32 n).val = n := by
  unfold u32
  simp only [UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem u32_self (x : U32) : u32 x.val = x := by
  have hb : x.val < 2 ^ 32 := by
    first | scalar_tac | (have := x.hBounds; simpa using this)
  apply UScalar.eq_of_val_eq
  exact u32_val' _ hb

/-- word `i` of a 32-byte digest encoding: `u32::from_le_bytes(bytes[4i..4i+4])` -/
def dw (l : List UInt8) (i : Nat) : Nat := le (sl l (4 * i) (4 * i + 4))

def mkDig (w : Nat → Nat) : Std.Array U32 8#usize :=
  Array.make 8#usize [u32 (w 0), u32 (w 1), u32 (w 2), u32 (w 3), u32 (w 4), u32 (w 5),
    u32 (w 6), u32 (w 7)]

/-- aspis_statement::decode_digest_canonical on a 32-byte encoding (frozen
atomic_statement.rs:91-111): eight `M31::from_le_bytes` (value < 2147483647 else Err). -/
def decDig (l : List UInt8) : Option (Std.Array U32 8#usize) :=
  if dw l 0 < 2147483647 ∧ dw l 1 < 2147483647 ∧ dw l 2 < 2147483647 ∧ dw l 3 < 2147483647 ∧
     dw l 4 < 2147483647 ∧ dw l 5 < 2147483647 ∧ dw l 6 < 2147483647 ∧ dw l 7 < 2147483647
  then some (mkDig (dw l)) else none

theorem all8_iff (w : Nat → Nat) :
    (w 0 < 2147483647 ∧ w 1 < 2147483647 ∧ w 2 < 2147483647 ∧ w 3 < 2147483647 ∧
      w 4 < 2147483647 ∧ w 5 < 2147483647 ∧ w 6 < 2147483647 ∧ w 7 < 2147483647) ↔
    ∀ j, j < 8 → w j < 2147483647 := by
  constructor
  · intro h j hj
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    all_goals assumption
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
      h 5 (by omega), h 6 (by omega), h 7 (by omega)⟩

theorem decDig_some (l : List UInt8) (h : ∀ j, j < 8 → dw l j < 2147483647) :
    decDig l = some (mkDig (dw l)) := by
  unfold decDig
  rw [if_pos ((all8_iff (dw l)).2 h)]

theorem decDig_none (l : List UInt8) (h : ¬ ∀ j, j < 8 → dw l j < 2147483647) :
    decDig l = none := by
  unfold decDig
  rw [if_neg (fun hh => h ((all8_iff (dw l)).1 hh))]

/-- the digest sits at offset s of a longer byte list -/
def dwAt (bytes : List UInt8) (s i : Nat) : Nat := le (sl bytes (s + 4 * i) (s + 4 * i + 4))

theorem sl_sl (l : List UInt8) (s i : Nat) (hi : i < 8) :
    sl (sl l s (s + 32)) (4 * i) (4 * i + 4) = sl l (s + 4 * i) (s + 4 * i + 4) := by
  apply List.ext_getElem?
  intro t
  unfold sl
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases ht : t < 4
  · have h2 : 4 * i + t < 32 := by omega
    simp only [ht, h2, if_true, Nat.add_assoc]
  · simp only [ht, if_false]

theorem dw_sl (l : List UInt8) (s i : Nat) (hi : i < 8) :
    dw (sl l s (s + 32)) i = dwAt l s i := by
  unfold dw dwAt
  rw [sl_sl l s i hi]

theorem digest_body_end (b : Slice U8) (s : Usize) (out : Std.Array U32 8#usize) (i : Usize)
    (h : ¬ i.val < 8) :
    NCV_Reference.digest_loop.body b s out i = ok (done (out, none)) := by
  have hge := not_lt8 i h
  unfold NCV_Reference.digest_loop.body
  simp only [hge, if_false]

theorem digest_body_spec (b : Slice U8) (s : Usize) (out : Std.Array U32 8#usize) (i : Usize)
    (hs : s.val + 32 ≤ b.val.length) (hi : i.val < 8) :
    ∃ x : U32, x.val = dwAt (bytesOf b) s.val i.val ∧
      (x.val < 2147483647 → ∀ c : Usize, (i + 1#usize : Result Usize) = ok c →
        NCV_Reference.digest_loop.body b s out i = ok (cont (out.set i x, c))) ∧
      (¬ x.val < 2147483647 →
        NCV_Reference.digest_loop.body b s out i = ok (done (out, some (core.result.Result.Err ())))) := by
  have hb := b.property
  have hlt := lt8 i hi
  obtain ⟨i1, e1, v1⟩ := mul_ok 4#usize i (by rw [four_val]; scalar_tac)
  obtain ⟨i2, e2, v2⟩ := add_ok s i1 (by rw [v1, four_val]; scalar_tac)
  have h2 : i2.val + 4 ≤ b.val.length := by rw [v2, v1, four_val]; omega
  obtain ⟨x, ex, vx⟩ := word32_eq b i2 h2
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [vx]
    unfold dwAt bytesOf
    rw [v2, v1, four_val]
  · intro hx c hc
    have hnge : ¬ (x ≥ 2147483647#u32) := by scalar_tac
    have hia : i.val < out.val.length := by rw [dlen]; exact hi
    obtain ⟨nv, hnv, hv⟩ := WP.spec_imp_exists (Array.update_spec out i x hia)
    unfold NCV_Reference.digest_loop.body
    simp only [hlt, if_true, bind_tc_ok, e1, e2, ex, hnge, if_false, hnv, hv, hc]
  · intro hx
    have hge : x ≥ 2147483647#u32 := by scalar_tac
    unfold NCV_Reference.digest_loop.body
    simp only [hlt, if_true, bind_tc_ok, e1, e2, ex, hge]

theorem digest_loop_eq (b : Slice U8) (s : Usize) (hs : s.val + 32 ≤ b.val.length) :
    ∀ (k : Nat) (out : Std.Array U32 8#usize) (i : Usize), 8 - i.val = k → i.val ≤ 8 →
    (∀ j, j < i.val → ∃ y : U32, out.val[j]? = some y ∧ y.val = dwAt (bytesOf b) s.val j) →
    ∃ (out' : Std.Array U32 8#usize) (r : Option (core.result.Result (Std.Array U32 8#usize) Unit)),
      NCV_Reference.digest_loop b s out i = ok (out', r) ∧
      ((r = none ∧ (∀ j, i.val ≤ j → j < 8 → dwAt (bytesOf b) s.val j < 2147483647) ∧
        ∀ j, j < 8 → ∃ y : U32, out'.val[j]? = some y ∧ y.val = dwAt (bytesOf b) s.val j) ∨
       (r = some (core.result.Result.Err ()) ∧
        ∃ j, i.val ≤ j ∧ j < 8 ∧ ¬ dwAt (bytesOf b) s.val j < 2147483647)) := by
  intro k
  induction k with
  | zero =>
    intro out i hk hi inv
    refine ⟨out, none, ?_, Or.inl ⟨rfl, fun j hj hj' => by omega, fun j hj => inv j (by omega)⟩⟩
    unfold NCV_Reference.digest_loop
    rw [loop.eq_def]
    simp only [digest_body_end b s out i (by omega)]
  | succ k ih =>
    intro out i hk hi inv
    have hi8 : i.val < 8 := by omega
    obtain ⟨c, hc, hcv⟩ := add_ok i 1#usize (by scalar_tac)
    have hcv' : c.val = i.val + 1 := by rw [hcv, one_val]
    obtain ⟨x, hxv, hok, hbad⟩ := digest_body_spec b s out i hs hi8
    by_cases hx : x.val < 2147483647
    · have hal := dlen out
      have inv' : ∀ j, j < c.val → ∃ y : U32, (out.set i x).val[j]? = some y ∧
          y.val = dwAt (bytesOf b) s.val j := by
        intro j hj
        have hset : (out.set i x).val = out.val.set i.val x := rfl
        rw [hset, List.getElem?_set]
        by_cases hji : i.val = j
        · subst hji
          exact ⟨x, by simp [hal, hi8], hxv⟩
        · have hj' : j < i.val := by omega
          obtain ⟨y, hy1, hy2⟩ := inv j hj'
          exact ⟨y, by simp [hji, hy1], hy2⟩
      obtain ⟨out', r, hr, hcases⟩ := ih (out.set i x) c (by omega) (by omega) inv'
      refine ⟨out', r, ?_, ?_⟩
      · unfold NCV_Reference.digest_loop
        rw [loop.eq_def]
        simp only [hok hx c hc]
        unfold NCV_Reference.digest_loop at hr
        exact hr
      · rcases hcases with ⟨hr1, hall, hfill⟩ | ⟨hr1, j, hj1, hj2, hj3⟩
        · refine Or.inl ⟨hr1, ?_, hfill⟩
          intro j hj hj'
          by_cases hji : j = i.val
          · subst hji; rw [← hxv]; exact hx
          · exact hall j (by omega) hj'
        · exact Or.inr ⟨hr1, j, by omega, hj2, hj3⟩
    · refine ⟨out, some (core.result.Result.Err ()), ?_, Or.inr ⟨rfl, i.val, le_refl _, hi8, ?_⟩⟩
      · unfold NCV_Reference.digest_loop
        rw [loop.eq_def]
        simp only [hbad hx]
      · rw [← hxv]; exact hx

#print axioms digest_loop_eq

theorem mkDig_ext (w : Nat → Nat) (out : Std.Array U32 8#usize)
    (h : ∀ j, j < 8 → ∃ y : U32, out.val[j]? = some y ∧ y.val = w j)
    (hw : ∀ j, j < 8 → w j < 2 ^ 32) : out = mkDig w := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro n
  by_cases hn : n < 8
  · obtain ⟨y, hy1, hy2⟩ := h n hn
    have hy : y = u32 (w n) := by
      apply UScalar.eq_of_val_eq
      rw [hy2, u32_val' _ (hw n hn)]
    rw [hy1, hy]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    all_goals rfl
  · have h1 : out.val[n]? = none := List.getElem?_eq_none (by rw [dlen]; omega)
    have h2 : (mkDig w).val[n]? = none := by
      apply List.getElem?_eq_none
      show 8 ≤ n
      omega
    rw [h1]
    exact h2.symm

theorem digest_eq (b : Slice U8) (s : Usize) (hs : s.val + 32 ≤ b.val.length) :
    NCV_Reference.digest b s =
      ok (match decDig (sl (bytesOf b) s.val (s.val + 32)) with
          | some d => core.result.Result.Ok d
          | none => core.result.Result.Err ()) := by
  have hw : ∀ j, j < 8 → dw (sl (bytesOf b) s.val (s.val + 32)) j = dwAt (bytesOf b) s.val j :=
    fun j hj => dw_sl _ _ _ hj
  unfold NCV_Reference.digest
  obtain ⟨out', r, hr, hcases⟩ := digest_loop_eq b s hs 8 (Array.repeat 8#usize 0#u32) 0#usize
    (by simp) (by simp) (fun j hj => absurd hj (by simp))
  have h0v : (0#usize).val = 0 := by simp
  simp only [h0v] at hcases
  dsimp only
  simp only [hr, bind_tc_ok]
  by_cases hall : ∀ j, j < 8 → dwAt (bytesOf b) s.val j < 2147483647
  · rcases hcases with ⟨hr1, _, hfill⟩ | ⟨hr1, j, _, hj2, hj3⟩
    · subst hr1
      have hd : decDig (sl (bytesOf b) s.val (s.val + 32)) =
          some (mkDig (dw (sl (bytesOf b) s.val (s.val + 32)))) :=
        decDig_some _ (fun j hj => by rw [hw j hj]; exact hall j hj)
      have he : out' = mkDig (dw (sl (bytesOf b) s.val (s.val + 32))) := by
        apply mkDig_ext
        · intro j hj
          obtain ⟨y, h1, h2⟩ := hfill j hj
          exact ⟨y, h1, by rw [hw j hj]; exact h2⟩
        · intro j hj
          rw [hw j hj]
          have := hall j hj
          omega
      rw [hd, he]
    · exact absurd (hall j hj2) hj3
  · rcases hcases with ⟨hr1, hall', _⟩ | ⟨hr1, j, _, hj2, hj3⟩
    · exact absurd (fun j hj => hall' j (by omega) hj) hall
    · subst hr1
      have hn : decDig (sl (bytesOf b) s.val (s.val + 32)) = none :=
        decDig_none _ (fun hh => hj3 (by rw [← hw j hj2]; exact hh j hj2))
      rw [hn]
end PCVY_Op50
