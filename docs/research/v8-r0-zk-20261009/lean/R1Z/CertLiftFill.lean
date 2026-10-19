import R1Z.CertBuildFill

/-! D59.2 builder 2: the extracted `fill_lo` lays out the 16 C1 lifts and the H1
lift row-major: entry `l·w² + i·w + x` is a `c1_entry` of row `sel1[l·w + x]` at
coordinate `i` (`C1At`), and entry `16·w² + i·wh + x` an `h1_entry` of
`(selh[x] / 4, selh[x] mod 4)` (`H1At`). -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck
open scoped BigOperators

variable (al zz tr sx sy inact sel1 selh : Slice U32)

/-- The natural value of a slice entry. -/
def gNL (s : Slice U32) (k : ℕ) : ℕ := (s.val[k]!).val

/-- Entry `(i, s)` of C1 lift `l` (width `w`). -/
def C1At (l w i s : ℕ) (v : U32) : Prop :=
  ∃ rr ii : Usize, rr.val = gNL sel1 (l * w + s) ∧ ii.val = i ∧
    R1CertBuild.c1_entry al zz tr sx sy inact rr ii = ok v

/-- Entry `(i, s)` of the H1 lift. -/
def H1At (i s : ℕ) (v : U32) : Prop :=
  ∃ rr kk ii : Usize, rr.val = gNL selh s / 4 ∧ kk.val = gNL selh s % 4 ∧ ii.val = i ∧
    R1CertBuild.h1_entry al zz tr sx sy inact rr kk ii = ok v

theorem c1_row_spec (l w i : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (x : Usize) (res : alloc.vec.Vec U32), x.val + m = w.val →
      R1CertBuild.c1_row_loop al zz tr sx sy inact sel1 l w i out x = ok res →
      res.val.length = out.val.length + m ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ s, x.val ≤ s → s < w.val →
          C1At al zz tr sx sy inact sel1 l.val w.val i.val s (res.val[out.val.length + (s - x.val)]!)
  | 0, out, x, res, hm, h => by
      rw [R1CertBuild.c1_row_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun s h1 h2 => by omega⟩
  | m + 1, out, x, res, hm, h => by
      rw [R1CertBuild.c1_row_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨x1, hx1, h⟩ := bind_eq_ok h
      have hx1v : x1.val = x.val + 1 := by rw [add_ok hx1]; simp
      have eo := push_ok hout1
      have hlen : out1.val.length = out.val.length + 1 := by rw [eo]; simp
      obtain ⟨L, P1, P2⟩ := c1_row_spec l w i m out1 x1 res (by omega) h
      refine ⟨by rw [L, hlen]; omega, fun y hy => by rw [P1 y (by omega), eo, get_append_left _ _ hy],
        fun s h1 h2 => ?_⟩
      by_cases es : s = x.val
      · subst es
        rw [Nat.sub_self, add_zero, P1 _ (by omega), eo, get_append_len]
        refine ⟨i4, i, ?_, rfl, hi5⟩
        rw [(ok_inj hi4).symm, castUs, (index_ok hi3).2, add_ok hi2, mul_ok hi1]
        rfl
      · have := P2 s (by omega) h2
        rw [hlen, hx1v, show out.val.length + 1 + (s - (x.val + 1)) = out.val.length + (s - x.val) by omega]
          at this
        exact this

theorem c1_lift_spec (l w : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (i : Usize) (res : alloc.vec.Vec U32), i.val + m = w.val →
      R1CertBuild.c1_lift_loop al zz tr sx sy inact sel1 l w out i = ok res →
      res.val.length = out.val.length + m * w.val ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ i', i.val ≤ i' → i' < w.val → ∀ s, s < w.val →
          C1At al zz tr sx sy inact sel1 l.val w.val i' s (res.val[out.val.length + (i' - i.val) * w.val + s]!)
  | 0, out, i, res, hm, h => by
      rw [R1CertBuild.c1_lift_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun i' h1 h2 => by omega⟩
  | m + 1, out, i, res, hm, h => by
      rw [R1CertBuild.c1_lift_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      have hi1v : i1.val = i.val + 1 := by rw [add_ok hi1]; simp
      obtain ⟨L1, Q1, Q2⟩ := c1_row_spec al zz tr sx sy inact sel1 l w i w.val out 0#usize out1 (by simp) hout1
      obtain ⟨L, P1, P2⟩ := c1_lift_spec l w m out1 i1 res (by omega) h
      refine ⟨by rw [L, L1]; ring, fun y hy => by rw [P1 y (by omega), Q1 y hy], fun i' h1 h2 s hs => ?_⟩
      by_cases ei : i' = i.val
      · subst ei
        have := Q2 s (by simp) hs
        rw [P1 _ (by rw [L1]; simp; omega)]
        simpa using this
      · have := P2 i' (by omega) h2 s hs
        rw [L1, hi1v, show out.val.length + w.val + (i' - (i.val + 1)) * w.val + s =
          out.val.length + (i' - i.val) * w.val + s by
            rw [show i' - i.val = (i' - (i.val + 1)) + 1 by omega]; ring] at this
        exact this

theorem c1_lifts_spec (w : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (l : Usize) (res : alloc.vec.Vec U32), l.val + m = 16 →
      R1CertBuild.c1_lifts_loop al zz tr sx sy inact sel1 w out l = ok res →
      res.val.length = out.val.length + m * (w.val * w.val) ∧
        (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ l', l.val ≤ l' → l' < 16 → ∀ i, i < w.val → ∀ s, s < w.val →
          C1At al zz tr sx sy inact sel1 l' w.val i s
            (res.val[out.val.length + (l' - l.val) * (w.val * w.val) + i * w.val + s]!)
  | 0, out, l, res, hm, h => by
      rw [R1CertBuild.c1_lifts_loop, if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun l' h1 h2 => by omega⟩
  | m + 1, out, l, res, hm, h => by
      rw [R1CertBuild.c1_lifts_loop, if_pos (by rw [UScalar.lt_equiv]; simp; omega)] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨l1, hl1, h⟩ := bind_eq_ok h
      have hl1v : l1.val = l.val + 1 := by rw [add_ok hl1]; simp
      obtain ⟨L1, Q1, Q2⟩ := c1_lift_spec al zz tr sx sy inact sel1 l w w.val out 0#usize out1 (by simp) hout1
      obtain ⟨L, P1, P2⟩ := c1_lifts_spec w m out1 l1 res (by omega) h
      refine ⟨by rw [L, L1]; ring, fun y hy => by rw [P1 y (by omega), Q1 y hy],
        fun l' h1 h2 i hi s hs => ?_⟩
      by_cases el : l' = l.val
      · subst el
        have := Q2 i (by simp) hi s hs
        have hlt : out.val.length + i * w.val + s < out1.val.length := by
          rw [L1]
          have : i * w.val + s < w.val * w.val := by nlinarith
          omega
        rw [P1 _ (by simpa using hlt)]
        simpa using this
      · have := P2 l' (by omega) h2 i hi s hs
        rw [L1, hl1v, show out.val.length + w.val * w.val + (l' - (l.val + 1)) * (w.val * w.val) + i * w.val + s =
          out.val.length + (l' - l.val) * (w.val * w.val) + i * w.val + s by
            rw [show l' - l.val = (l' - (l.val + 1)) + 1 by omega]; ring] at this
        exact this

theorem h1_row_spec (w i : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (x : Usize) (res : alloc.vec.Vec U32), x.val + m = w.val →
      R1CertBuild.h1_row_loop al zz tr sx sy inact selh w i out x = ok res →
      res.val.length = out.val.length + m ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ s, x.val ≤ s → s < w.val →
          H1At al zz tr sx sy inact selh i.val s (res.val[out.val.length + (s - x.val)]!)
  | 0, out, x, res, hm, h => by
      rw [R1CertBuild.h1_row_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun s h1 h2 => by omega⟩
  | m + 1, out, x, res, hm, h => by
      rw [R1CertBuild.h1_row_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨e, he, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨x1, hx1, h⟩ := bind_eq_ok h
      have hx1v : x1.val = x.val + 1 := by rw [add_ok hx1]; simp
      have eo := push_ok hout1
      have hlen : out1.val.length = out.val.length + 1 := by rw [eo]; simp
      obtain ⟨L, P1, P2⟩ := h1_row_spec w i m out1 x1 res (by omega) h
      refine ⟨by rw [L, hlen]; omega, fun y hy => by rw [P1 y (by omega), eo, get_append_left _ _ hy],
        fun s h1 h2 => ?_⟩
      by_cases es : s = x.val
      · subst es
        rw [Nat.sub_self, add_zero, P1 _ (by omega), eo, get_append_len]
        have ee : e.val = gNL selh x.val := by
          rw [(ok_inj he).symm, castUs, (index_ok hi1).2]; rfl
        have four : (4#usize : Usize).val ≠ 0 := by simp
        refine ⟨i2, i3, i, ?_, ?_, rfl, hi4⟩
        · rw [div_ok four hi2, ee]; simp
        · rw [rem_ok four hi3, ee]; simp
      · have := P2 s (by omega) h2
        rw [hlen, hx1v, show out.val.length + 1 + (s - (x.val + 1)) = out.val.length + (s - x.val) by omega]
          at this
        exact this

theorem h1_lift_spec (w : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (i : Usize) (res : alloc.vec.Vec U32), i.val + m = w.val →
      R1CertBuild.h1_lift_loop al zz tr sx sy inact selh w out i = ok res →
      res.val.length = out.val.length + m * w.val ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ i', i.val ≤ i' → i' < w.val → ∀ s, s < w.val →
          H1At al zz tr sx sy inact selh i' s (res.val[out.val.length + (i' - i.val) * w.val + s]!)
  | 0, out, i, res, hm, h => by
      rw [R1CertBuild.h1_lift_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun i' h1 h2 => by omega⟩
  | m + 1, out, i, res, hm, h => by
      rw [R1CertBuild.h1_lift_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      have hi1v : i1.val = i.val + 1 := by rw [add_ok hi1]; simp
      obtain ⟨L1, Q1, Q2⟩ := h1_row_spec al zz tr sx sy inact selh w i w.val out 0#usize out1 (by simp) hout1
      obtain ⟨L, P1, P2⟩ := h1_lift_spec w m out1 i1 res (by omega) h
      refine ⟨by rw [L, L1]; ring, fun y hy => by rw [P1 y (by omega), Q1 y hy], fun i' h1 h2 s hs => ?_⟩
      by_cases ei : i' = i.val
      · subst ei
        have := Q2 s (by simp) hs
        rw [P1 _ (by rw [L1]; simp; omega)]
        simpa using this
      · have := P2 i' (by omega) h2 s hs
        rw [L1, hi1v, show out.val.length + w.val + (i' - (i.val + 1)) * w.val + s =
          out.val.length + (i' - i.val) * w.val + s by
            rw [show i' - i.val = (i' - (i.val + 1)) + 1 by omega]; ring] at this
        exact this

/-- **`fill_lo`**: the C1 lifts then the H1 lift. -/
theorem fill_lo_spec {nq : Usize} {res : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_lo al zz tr sx sy inact sel1 selh nq = ok res) :
    (∀ l, l < 16 → ∀ i, i < 24 + 4 * nq.val → ∀ s, s < 24 + 4 * nq.val →
      C1At al zz tr sx sy inact sel1 l (24 + 4 * nq.val) i s
        (res.val[l * ((24 + 4 * nq.val) * (24 + 4 * nq.val)) + i * (24 + 4 * nq.val) + s]!)) ∧
    (∀ i, i < 24 + 16 * nq.val → ∀ s, s < 24 + 16 * nq.val →
      H1At al zz tr sx sy inact selh i s
        (res.val[16 * ((24 + 4 * nq.val) * (24 + 4 * nq.val)) + i * (24 + 16 * nq.val) + s]!)) := by
  unfold R1CertBuild.fill_lo at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨out, hout, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  have e1 : i1.val = 24 + 4 * nq.val := by rw [add_ok hi1, mul_ok hi]; simp
  have e3 : i3.val = 24 + 16 * nq.val := by rw [add_ok hi3, mul_ok hi2]; simp
  obtain ⟨L1, -, C⟩ := c1_lifts_spec al zz tr sx sy inact sel1 i1 16 (alloc.vec.Vec.new U32) 0#usize out
    (by simp) hout
  obtain ⟨-, Q1, H⟩ := h1_lift_spec al zz tr sx sy inact selh i3 i3.val out 0#usize res (by simp) h
  have hl0 : (alloc.vec.Vec.new U32).val.length = 0 := rfl
  rw [hl0, zero_add, e1] at L1
  refine ⟨fun l hl i hi s hs => ?_, fun i hi s hs => ?_⟩
  · have := C l (by simp) hl i (by rw [e1]; exact hi) s (by rw [e1]; exact hs)
    rw [hl0, e1] at this
    have hlt : l * ((24 + 4 * nq.val) * (24 + 4 * nq.val)) + i * (24 + 4 * nq.val) + s < out.val.length := by
      rw [L1]
      have : i * (24 + 4 * nq.val) + s < (24 + 4 * nq.val) * (24 + 4 * nq.val) := by nlinarith
      nlinarith
    rw [Q1 _ hlt]
    simpa using this
  · have := H i (by simp) (by rw [e3]; exact hi) s (by rw [e3]; exact hs)
    rw [L1, e3] at this
    simpa using this

#print axioms c1_lifts_spec
#print axioms h1_lift_spec
#print axioms fill_lo_spec

end R1Z.CertBuild
