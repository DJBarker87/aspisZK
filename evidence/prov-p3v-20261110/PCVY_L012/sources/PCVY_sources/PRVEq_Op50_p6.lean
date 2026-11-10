import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p5
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le)

theorem two_val : (2#usize).val = 2 := by simp
theorem three_val : (3#usize).val = 3 := by simp
theorem four_val : (4#usize).val = 4 := by simp
theorem five_val : (5#usize).val = 5 := by simp
theorem six_val : (6#usize).val = 6 := by simp
theorem seven_val : (7#usize).val = 7 := by simp

/-- byte carrier from the Aeneas byte to the transcription's byte -/
def bt (x : U8) : UInt8 := UInt8.ofNat x.val

theorem bt_toNat (x : U8) : (bt x).toNat = x.val := by
  have hx : x.val < 256 := by scalar_tac
  unfold bt
  first
  | (rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt hx)
  | (simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hx])
  | (simp [UInt8.ofNat, Nat.mod_eq_of_lt hx])

theorem bt_inj (x y : U8) (h : bt x = bt y) : x = y := by
  have := congrArg UInt8.toNat h
  rw [bt_toNat, bt_toNat] at this
  exact UScalar.eq_of_val_eq this

/-! ## 2. zero_loop / zero -/

def Zs (l : List U8) : Prop := ∀ x ∈ l, x = 0#u8

instance (l : List U8) : Decidable (Zs l) := by unfold Zs; infer_instance

theorem zero_body_end (b : Slice U8) (i : Usize) (h : ¬ i.val < b.val.length) :
    NCV_Reference.zero_loop.body b i = ok (done none) := by
  have hge := not_lt_len b i h
  unfold NCV_Reference.zero_loop.body
  simp only [hge, if_false]

theorem zero_body_diff (b : Slice U8) (i : Usize) (hi : i.val < b.val.length)
    (hne : b.val[i.val]'hi ≠ 0#u8) :
    NCV_Reference.zero_loop.body b i = ok (done (some false)) := by
  have hlt := lt_len b i hi
  have hb' : (b.val[i.val]'hi != 0#u8) = true := by simp [hne]
  unfold NCV_Reference.zero_loop.body
  simp only [hlt, if_true, bind_tc_ok, idx_slice b i hi, hb']

theorem zero_body_same (b : Slice U8) (i c : Usize) (hi : i.val < b.val.length)
    (hne : b.val[i.val]'hi = 0#u8) (hc : (i + 1#usize : Result Usize) = ok c) :
    NCV_Reference.zero_loop.body b i = ok (cont c) := by
  have hlt := lt_len b i hi
  have hb' : (b.val[i.val]'hi != 0#u8) = false := by simp [hne]
  unfold NCV_Reference.zero_loop.body
  simp only [hlt, if_true, bind_tc_ok, idx_slice b i hi, hb', Bool.false_eq_true, if_false, hc]

theorem zero_loop_eq (b : Slice U8) :
    ∀ (k : Nat) (i : Usize), b.val.length - i.val = k → i.val ≤ b.val.length →
    NCV_Reference.zero_loop b i = ok (if Zs (b.val.drop i.val) then none else some false) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    have e1 : b.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    have hz : Zs (b.val.drop i.val) := by rw [e1]; intro x hx; cases hx
    unfold NCV_Reference.zero_loop
    rw [loop.eq_def]
    simp only [zero_body_end b i (by omega), hz, if_true]
  | succ k ih =>
    intro i hk hi
    obtain ⟨c, hc, hcv⟩ := add_ok i 1#usize (by scalar_tac)
    have hcv' : c.val = i.val + 1 := by rw [hcv, one_val]
    have eb : b.val.drop i.val = b.val[i.val]'(by omega) :: b.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons (by omega)
    have ih' := ih c (by omega) (by omega)
    rw [hcv'] at ih'
    unfold NCV_Reference.zero_loop
    rw [loop.eq_def]
    by_cases hne : b.val[i.val]'(by omega) = 0#u8
    · simp only [zero_body_same b i c (by omega) hne hc]
      unfold NCV_Reference.zero_loop at ih'
      have key : Zs (b.val.drop i.val) ↔ Zs (b.val.drop (i.val + 1)) := by
        rw [eb]; unfold Zs
        simp only [List.mem_cons, forall_eq_or_imp, hne, true_and]
      rw [ih']
      simp only [key]
    · simp only [zero_body_diff b i (by omega) hne]
      have key : ¬ Zs (b.val.drop i.val) := by
        rw [eb]; unfold Zs
        simp only [List.mem_cons, forall_eq_or_imp, not_and]
        intro h; exact absurd h hne
      simp only [key, if_false]

theorem zero_eq (b : Slice U8) :
    NCV_Reference.zero b = ok (decide (Zs b.val)) := by
  unfold NCV_Reference.zero
  have h0 := zero_loop_eq b b.val.length (0#usize) (by simp) (by simp)
  rw [h0]
  by_cases hz : Zs b.val
  · simp [hz]
  · have : ¬ Zs (b.val.drop 0) := by simpa using hz
    simp [this, hz]

#print axioms zero_loop_eq
#print axioms zero_eq

/-! ## 3. bytes32_loop / bytes32 -/

theorem bytes32_body_end (b : Slice U8) (s : Usize) (a : Array U8 32#usize) (i : Usize)
    (h : ¬ i.val < 32) :
    NCV_Reference.bytes32_loop.body b s a i = ok (done a) := by
  have hge : ¬ (i < 32#usize) := by scalar_tac
  unfold NCV_Reference.bytes32_loop.body
  simp only [hge, if_false]

theorem bytes32_body_step (b : Slice U8) (s : Usize) (a : Array U8 32#usize) (i j c : Usize)
    (hi : i.val < 32) (hj : (s + i : Result Usize) = ok j) (hjb : j.val < b.val.length)
    (hc : (i + 1#usize : Result Usize) = ok c) :
    NCV_Reference.bytes32_loop.body b s a i = ok (cont (a.set i (b.val[j.val]'hjb), c)) := by
  have hlt : i < 32#usize := by scalar_tac
  have hia : i.val < a.length := by have := a.property; scalar_tac
  obtain ⟨nv, hnv, hv⟩ := WP.spec_imp_exists (Array.update_spec a i (b.val[j.val]'hjb) hia)
  unfold NCV_Reference.bytes32_loop.body
  simp only [hlt, if_true, bind_tc_ok, hj, idx_slice b j hjb, hnv, hv, hc]

theorem bytes32_loop_eq (b : Slice U8) (s : Usize) (hs : s.val + 32 ≤ b.val.length) :
    ∀ (k : Nat) (a : Array U8 32#usize) (i : Usize), 32 - i.val = k → i.val ≤ 32 →
    (∀ j, j < i.val → a.val[j]? = b.val[s.val + j]?) →
    ∃ r : Array U8 32#usize, NCV_Reference.bytes32_loop b s a i = ok r ∧
      r.val = (b.val.drop s.val).take 32 := by
  intro k
  induction k with
  | zero =>
    intro a i hk hi inv
    refine ⟨a, ?_, ?_⟩
    · unfold NCV_Reference.bytes32_loop
      rw [loop.eq_def]
      simp only [bytes32_body_end b s a i (by omega)]
    · have hal : a.val.length = 32 := by have := a.property; simpa using this
      apply List.ext_getElem?
      intro n
      by_cases hn : n < 32
      · have := inv n (by omega)
        rw [this, List.getElem?_take, List.getElem?_drop]
        simp [hn, Nat.add_comm]
      · rw [List.getElem?_take]
        simp [hn]
  | succ k ih =>
    intro a i hk hi inv
    have hi32 : i.val < 32 := by omega
    obtain ⟨c, hc, hcv⟩ := add_ok i 1#usize (by scalar_tac)
    have hcv' : c.val = i.val + 1 := by rw [hcv, one_val]
    obtain ⟨j, hj, hjv⟩ := add_ok s i (by have := b.property; scalar_tac)
    have hjb : j.val < b.val.length := by omega
    have hal : a.val.length = 32 := by have := a.property; simpa using this
    have inv' : ∀ m, m < c.val → (a.set i (b.val[j.val]'hjb)).val[m]? = b.val[s.val + m]? := by
      intro m hm
      have hset : (a.set i (b.val[j.val]'hjb)).val = a.val.set i.val (b.val[j.val]'hjb) := rfl
      rw [hset, List.getElem?_set]
      by_cases hmi : i.val = m
      · subst hmi
        simp [hal, hjv, hi32, List.getElem?_eq_getElem hjb]
      · have : m < i.val := by omega
        simp [hmi, inv m this]
    obtain ⟨r, hr, hrv⟩ := ih (a.set i (b.val[j.val]'hjb)) c (by omega) (by omega) inv'
    refine ⟨r, ?_, hrv⟩
    unfold NCV_Reference.bytes32_loop
    rw [loop.eq_def]
    simp only [bytes32_body_step b s a i j c hi32 hj hjb hc]
    unfold NCV_Reference.bytes32_loop at hr
    exact hr

theorem bytes32_eq (b : Slice U8) (s : Usize) (hs : s.val + 32 ≤ b.val.length) :
    ∃ r : Array U8 32#usize, NCV_Reference.bytes32 b s = ok r ∧
      r.val = (b.val.drop s.val).take 32 := by
  unfold NCV_Reference.bytes32
  exact bytes32_loop_eq b s hs 32 (Array.repeat 32#usize 0#u8) 0#usize (by simp) (by simp)
    (fun j hj => absurd hj (by simp))

#print axioms bytes32_loop_eq
#print axioms bytes32_eq

/-! ## 4. little-endian words -/

theorem or_shl8 (x y : Nat) (hy : y < 256) : (x <<< 8) ||| y = y + 256 * x := by
  first
  | (rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hy)]; simp [Nat.shiftLeft_eq]; omega)

#check @Nat.shiftLeft_add_eq_or_of_lt
#check @BitVec.toNat_append
#check @BitVec.toNat_cast
#check @BitVec.fromLEBytes
end PCVY_Op50
