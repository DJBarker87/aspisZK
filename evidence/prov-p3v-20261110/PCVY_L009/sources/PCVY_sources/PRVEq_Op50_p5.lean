import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50

/-! ## 0. helpers -/

theorem add_ok (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, (a + b : Result Usize) = ok c ∧ c.val = a.val + b.val := by
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) h)
  exact ⟨z, hz, hv⟩

theorem mul_ok (a b : Usize) (h : a.val * b.val ≤ Usize.max) :
    ∃ c : Usize, (a * b : Result Usize) = ok c ∧ c.val = a.val * b.val := by
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (Usize.mul_spec (x := a) (y := b) h)
  exact ⟨z, hz, hv⟩

theorem idx_slice (b : Slice U8) (i : Usize) (h : i.val < b.val.length) :
    b.index_usize i = ok (b.val[i.val]'h) := by
  obtain ⟨x, hx, hv⟩ := WP.spec_imp_exists (Slice.index_usize_spec b i h)
  rw [hx, hv]

theorem lt_len (b : Slice U8) (i : Usize) (h : i.val < b.val.length) : i < Slice.len b := by
  scalar_tac

theorem not_lt_len (b : Slice U8) (i : Usize) (h : ¬ i.val < b.val.length) : ¬ (i < Slice.len b) := by
  scalar_tac

/-! ## 1. equal_loop / equal -/

theorem one_val : (1#usize).val = 1 := by simp

theorem equal_body_end (b v : Slice U8) (i : Usize) (h : ¬ i.val < b.val.length) :
    NCV_Reference.equal_loop.body b v i = ok (done none) := by
  have hge := not_lt_len b i h
  unfold NCV_Reference.equal_loop.body
  simp only [hge, if_false]

theorem equal_body_diff (b v : Slice U8) (i : Usize) (hi : i.val < b.val.length)
    (hv : i.val < v.val.length) (hne : b.val[i.val]'hi ≠ v.val[i.val]'hv) :
    NCV_Reference.equal_loop.body b v i = ok (done (some false)) := by
  have hlt := lt_len b i hi
  have hb' : (b.val[i.val]'hi != v.val[i.val]'hv) = true := by simp [hne]
  unfold NCV_Reference.equal_loop.body
  simp only [hlt, if_true, bind_tc_ok, idx_slice b i hi, idx_slice v i hv, hb']

theorem equal_body_same (b v : Slice U8) (i c : Usize) (hi : i.val < b.val.length)
    (hv : i.val < v.val.length) (hne : b.val[i.val]'hi = v.val[i.val]'hv)
    (hc : (i + 1#usize : Result Usize) = ok c) :
    NCV_Reference.equal_loop.body b v i = ok (cont c) := by
  have hlt := lt_len b i hi
  have hb' : (b.val[i.val]'hi != v.val[i.val]'hv) = false := by simp [hne]
  unfold NCV_Reference.equal_loop.body
  simp only [hlt, if_true, bind_tc_ok, idx_slice b i hi, idx_slice v i hv, hb',
    Bool.false_eq_true, if_false, hc]

theorem equal_loop_eq (b v : Slice U8) (hl : b.val.length = v.val.length) :
    ∀ (k : Nat) (i : Usize), b.val.length - i.val = k → i.val ≤ b.val.length →
    NCV_Reference.equal_loop b v i =
      ok (if b.val.drop i.val = v.val.drop i.val then none else some false) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    have e1 : b.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    have e2 : v.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    unfold NCV_Reference.equal_loop
    rw [loop.eq_def]
    simp only [equal_body_end b v i (by omega), e1, e2]
    simp
  | succ k ih =>
    intro i hk hi
    have hiv : i.val < v.val.length := by omega
    obtain ⟨c, hc, hcv⟩ := add_ok i 1#usize (by scalar_tac)
    have hcv' : c.val = i.val + 1 := by rw [hcv, one_val]
    have eb : b.val.drop i.val = b.val[i.val]'(by omega) :: b.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons (by omega)
    have ev : v.val.drop i.val = v.val[i.val]'hiv :: v.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hiv
    have ih' := ih c (by omega) (by omega)
    rw [hcv'] at ih'
    unfold NCV_Reference.equal_loop
    rw [loop.eq_def]
    by_cases hne : b.val[i.val]'(by omega) = v.val[i.val]'hiv
    · simp only [equal_body_same b v i c (by omega) hiv hne hc]
      unfold NCV_Reference.equal_loop at ih'
      have key : (b.val.drop i.val = v.val.drop i.val) ↔
          (b.val.drop (i.val + 1) = v.val.drop (i.val + 1)) := by
        rw [eb, ev]; simp [hne]
      rw [ih']
      simp only [key]
    · simp only [equal_body_diff b v i (by omega) hiv hne]
      have key : ¬ (b.val.drop i.val = v.val.drop i.val) := by
        rw [eb, ev]; simp [hne]
      simp only [key, if_false]

#print axioms equal_loop_eq

theorem equal_eq (b v : Slice U8) :
    NCV_Reference.equal b v = ok (decide (b.val = v.val)) := by
  unfold NCV_Reference.equal
  by_cases hl : b.val.length = v.val.length
  · have hn : ¬ (Slice.len b != Slice.len v) = true := by
      simp only [bne_iff_ne, ne_eq, not_not]
      apply UScalar.eq_of_val_eq
      simp [Slice.len_val, Slice.length, hl]
    have h0 := equal_loop_eq b v hl b.val.length (0#usize) (by simp) (by simp)
    simp only [hn, if_false, Bool.false_eq_true, bind_tc_ok]
    rw [h0]
    by_cases he : b.val = v.val
    · simp [he]
    · have : ¬ b.val.drop 0 = v.val.drop 0 := by simpa using he
      simp [this, he]
  · have hn : (Slice.len b != Slice.len v) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro h
      apply hl
      have := congrArg UScalar.val h
      simpa [Slice.len_val, Slice.length] using this
    have he : ¬ b.val = v.val := fun h => hl (by rw [h])
    simp [hn, he]

#print axioms equal_eq
end PCVY_Op50
