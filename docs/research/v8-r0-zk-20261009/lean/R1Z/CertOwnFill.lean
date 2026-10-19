import R1Z.CertLiftEntry

/-! D62 builder 3: the extracted `fill_own` lays out the own columns: entry
`t·os + i` is `own_val (kind t) (srow t) (slimb t) i`, which is the C1 value
balanced at row 0 (`own_c1`) for a mask-only lane, the H1 entry for G/D, and 0
beyond the lane's block width. -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck
open scoped BigOperators

variable (al zz tr sx sy inact kind srow slimb : Slice U32)

theorem own_c1_spec {r i : Usize} {v : U32} (h : R1CertBuild.own_c1 al zz tr sx sy inact r i = ok v) :
    ∃ o1 o2 : U32, R1CertBuild.c1_val al zz tr sx sy r i = ok o1 ∧
      (∃ dd : Usize, dd.val = 0 ∧ R1CertBuild.c1_val al zz tr sx sy dd i = ok o2) ∧
      (v.val : ZP) = (o1.val : ZP) - gs inact r.val * (o2.val : ZP) := by
  unfold R1CertBuild.own_c1 at h
  obtain ⟨o1, h1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨o2, h2, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  refine ⟨o1, o2, h1, ⟨_, by simp, h2⟩, ?_⟩
  rw [(fsub_spec h).2, (fmul_spec hi4).2, idx_z' hi2]

/-- Entry `i` of own column `t`. -/
def OwnAt (nq : ℕ) (t i : ℕ) (v : U32) : Prop :=
  ∃ kk rr ll ii wb we : Usize, kk.val = gNL kind t ∧ rr.val = gNL srow t ∧ ll.val = gNL slimb t ∧
    ii.val = i ∧ wb.val = 24 + 4 * nq ∧ we.val = 24 + 16 * nq ∧
    R1CertBuild.own_val al zz tr sx sy inact kk rr ll ii wb we = ok v

theorem own_col_spec (kk rr ll os wb we : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (i : Usize) (res : alloc.vec.Vec U32), i.val + m = os.val →
      R1CertBuild.own_col_loop al zz tr sx sy inact kk rr ll os wb we out i = ok res →
      res.val.length = out.val.length + m ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ s, i.val ≤ s → s < os.val → ∃ ii : Usize, ii.val = s ∧
          R1CertBuild.own_val al zz tr sx sy inact kk rr ll ii wb we = ok (res.val[out.val.length + (s - i.val)]!)
  | 0, out, i, res, hm, h => by
      rw [R1CertBuild.own_col_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun s h1 h2 => by omega⟩
  | m + 1, out, i, res, hm, h => by
      rw [R1CertBuild.own_col_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      have hi2v : i2.val = i.val + 1 := by rw [add_ok hi2]; simp
      have eo := push_ok hout1
      have hlen : out1.val.length = out.val.length + 1 := by rw [eo]; simp
      obtain ⟨L, P1, P2⟩ := own_col_spec kk rr ll os wb we m out1 i2 res (by omega) h
      refine ⟨by rw [L, hlen]; omega, fun y hy => by rw [P1 y (by omega), eo, get_append_left _ _ hy],
        fun s h1 h2 => ?_⟩
      by_cases es : s = i.val
      · subst es
        rw [Nat.sub_self, add_zero, P1 _ (by omega), eo, get_append_len]
        exact ⟨i, rfl, hi1⟩
      · obtain ⟨ii, hii, hv⟩ := P2 s (by omega) h2
        rw [hlen, hi2v, show out.val.length + 1 + (s - (i.val + 1)) = out.val.length + (s - i.val) by omega]
          at hv
        exact ⟨ii, hii, hv⟩

theorem fill_own_loop_spec (n os nq : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (t : Usize) (res : alloc.vec.Vec U32), t.val + m = n.val →
      R1CertBuild.fill_own_loop al zz tr sx sy inact kind srow slimb n os nq out t = ok res →
      res.val.length = out.val.length + m * os.val ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ t', t.val ≤ t' → t' < n.val → ∀ i, i < os.val →
          OwnAt al zz tr sx sy inact kind srow slimb nq.val t' i
            (res.val[out.val.length + (t' - t.val) * os.val + i]!)
  | 0, out, t, res, hm, h => by
      rw [R1CertBuild.fill_own_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun t' h1 h2 => by omega⟩
  | m + 1, out, t, res, hm, h => by
      rw [R1CertBuild.fill_own_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
      obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
      obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
      obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      have ht1v : t1.val = t.val + 1 := by rw [add_ok ht1]; simp
      obtain ⟨L1, Q1, Q2⟩ := own_col_spec al zz tr sx sy inact i1 i3 i5 os i7 i9 os.val out 0#usize out1
        (by simp) hout1
      obtain ⟨L, P1, P2⟩ := fill_own_loop_spec n os nq m out1 t1 res (by omega) h
      refine ⟨by rw [L, L1]; ring, fun y hy => by rw [P1 y (by omega), Q1 y hy], fun t' h1 h2 i' hi' => ?_⟩
      by_cases et : t' = t.val
      · subst et
        obtain ⟨ii, hii, hv⟩ := Q2 i' (by simp) hi'
        rw [P1 _ (by rw [L1]; simp; omega)]
        simp only [Nat.sub_self, zero_mul, add_zero]
        simp only [Nat.sub_zero, show (0#usize : Usize).val = 0 by simp] at hv
        refine ⟨i1, i3, i5, ii, i7, i9, ?_, ?_, ?_, hii, ?_, ?_, hv⟩
        · rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
        · rw [(ok_inj hi3).symm, castUs, (index_ok hi2).2]; rfl
        · rw [(ok_inj hi5).symm, castUs, (index_ok hi4).2]; rfl
        · rw [add_ok hi7, mul_ok hi6]; simp
        · rw [add_ok hi9, mul_ok hi8]; simp
      · have := P2 t' (by omega) h2 i' hi'
        rw [L1, ht1v, show out.val.length + os.val + (t' - (t.val + 1)) * os.val + i' =
          out.val.length + (t' - t.val) * os.val + i' by
            rw [show t' - t.val = (t' - (t.val + 1)) + 1 by omega]; ring] at this
        exact this

/-- **`fill_own`**: entry `t·os + i` is `own_val` of source `t` at `i`. -/
theorem fill_own_spec {n os nq : Usize} {res : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_own al zz tr sx sy inact kind srow slimb n os nq = ok res) :
    ∀ t, t < n.val → ∀ i, i < os.val →
      OwnAt al zz tr sx sy inact kind srow slimb nq.val t i (res.val[t * os.val + i]!) := by
  obtain ⟨-, -, P⟩ := fill_own_loop_spec al zz tr sx sy inact kind srow slimb n os nq n.val
    (alloc.vec.Vec.new U32) 0#usize res (by simp) h
  intro t ht i hi
  have := P t (by simp) ht i hi
  simpa using this

#print axioms own_c1_spec
#print axioms fill_own_spec

end R1Z.CertBuild
