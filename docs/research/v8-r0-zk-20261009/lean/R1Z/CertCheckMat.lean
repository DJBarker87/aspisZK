import R1Z.CertCheckKer

/-! D49.4 C3: the extracted matrix tests.

* `prod_spec`: `prod_ok` = `ok true` gives `A·B = C` entrywise over M31 (row-major
  at offsets);
* `id_spec`, `ech_spec`: identity / echelon-on-pivots entries;
* `perm_left_spec`, `perm_right_spec`: `tag` is a two-sided inverse of the
  column list `lst` on `0 … n-1`;
* `nvec_spec`: the supplied `n_f` matrix is `e_{fr f} - ∑_a E[a][fr f] e_{piv a}`
  in the `tag` form;
* `lifts_spec`: each lift block has `O·U = I` with `I` the identity. -/

set_option autoImplicit false

namespace R1Z.CertCheck
open Aeneas Aeneas.Std Result R1CertCheck
open scoped BigOperators

theorem fromBool_val (p : Prop) [Decidable p] :
    ((UScalar.cast_fromBool .U64 (decide p)).val : ZP) = if p then 1 else 0 := by
  rw [UScalar.cast_fromBool_val_eq]
  by_cases hp : p <;> simp [hp]

theorem one_val : (1#usize : Usize).val = 1 := by simp

theorem usz_eq {x y : Usize} : x = y ↔ x.val = y.val := UScalar.eq_equiv x y

theorem prod_row_loop_stop (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) :
    ∀ (ok1 : Bool) (j : Usize), ¬ j.val < nj.val → prod_row_ok_loop a ao b bo c co i nj len ok1 j = ok ok1 := by
  intro ok1 j hj
  rw [prod_row_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hj)]

theorem prod_row_loop_step (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) :
    ∀ (ok1 : Bool) (j : Usize) (r : Bool), j.val < nj.val →
      prod_row_ok_loop a ao b bo c co i nj len ok1 j = ok r →
      ∃ b' j', j'.val = j.val + 1 ∧ prod_row_ok_loop a ao b bo c co i nj len b' j' = ok r ∧
        (b' = true → ok1 = true ∧
          ∑ p ∈ Finset.range len.val, gs a (ao.val + i.val * len.val + p) * gs b (bo.val + j.val + p * nj.val)
            = gs c (co.val + i.val * nj.val + j.val)) := by
  intro ok1 j r hj h
  rw [prod_row_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hj)] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  obtain ⟨j1, hj1, h⟩ := bind_eq_ok h
  refine ⟨_, j1, add_ok hj1, h, fun hb => ?_⟩
  obtain ⟨hb1, heq⟩ := and_dec hb
  refine ⟨hb1, ?_⟩
  have hd := (dot_spec hi4).2
  rw [heq, (ok_inj hi9).symm, cast64, (index_ok hi8).2, add_ok hi7, add_ok hi6, mul_ok hi5,
    add_ok hi2, mul_ok hi1, add_ok hi3, one_val] at hd
  simp only [mul_one] at hd
  rw [← hd]
  rfl

theorem prod_row_spec {a b c : Slice U32} {ao bo co i nj len : Usize}
    (h : prod_row_ok a ao b bo c co i nj len = ok true) :
    ∀ j, j < nj.val →
      ∑ p ∈ Finset.range len.val, gs a (ao.val + i.val * len.val + p) * gs b (bo.val + j + p * nj.val)
        = gs c (co.val + i.val * nj.val + j) :=
  flag_loop0 (F := fun ok1 j => prod_row_ok_loop a ao b bo c co i nj len ok1 j)
    (prod_row_loop_stop a ao b bo c co i nj len) (prod_row_loop_step a ao b bo c co i nj len) h

theorem prod_loop_stop (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize) :
    ∀ (ok1 : Bool) (i : Usize), ¬ i.val < ni.val → prod_ok_loop a ao b bo c co ni nj len ok1 i = ok ok1 := by
  intro ok1 i hi
  rw [prod_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hi)]

theorem prod_loop_step (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize) :
    ∀ (ok1 : Bool) (i : Usize) (r : Bool), i.val < ni.val →
      prod_ok_loop a ao b bo c co ni nj len ok1 i = ok r →
      ∃ b' i', i'.val = i.val + 1 ∧ prod_ok_loop a ao b bo c co ni nj len b' i' = ok r ∧
        (b' = true → ok1 = true ∧ ∀ j, j < nj.val →
          ∑ p ∈ Finset.range len.val, gs a (ao.val + i.val * len.val + p) * gs b (bo.val + j + p * nj.val)
            = gs c (co.val + i.val * nj.val + j)) := by
  intro ok1 i r hi h
  rw [prod_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hi)] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  refine ⟨_, i1, add_ok hi1, h, fun hb => ?_⟩
  obtain ⟨hok, hb1t⟩ := and_true' hb
  exact ⟨hok, prod_row_spec (hb1t ▸ hb1)⟩

/-- `prod_ok`: `A·B = C` entrywise. -/
theorem prod_spec {a b c : Slice U32} {ao bo co ni nj len : Usize}
    (h : prod_ok a ao b bo c co ni nj len = ok true) :
    ∀ i, i < ni.val → ∀ j, j < nj.val →
      ∑ p ∈ Finset.range len.val, gs a (ao.val + i * len.val + p) * gs b (bo.val + j + p * nj.val)
        = gs c (co.val + i * nj.val + j) :=
  flag_loop0 (F := fun ok1 i => prod_ok_loop a ao b bo c co ni nj len ok1 i)
    (prod_loop_stop a ao b bo c co ni nj len) (prod_loop_step a ao b bo c co ni nj len) h

theorem id_row_loop_stop (c : Slice U32) (co i w : Usize) :
    ∀ (ok1 : Bool) (j : Usize), ¬ j.val < w.val → id_row_ok_loop c co i w ok1 j = ok ok1 := by
  intro ok1 j hj
  rw [id_row_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hj)]

theorem id_row_loop_step (c : Slice U32) (co i w : Usize) :
    ∀ (ok1 : Bool) (j : Usize) (r : Bool), j.val < w.val →
      id_row_ok_loop c co i w ok1 j = ok r →
      ∃ b' j', j'.val = j.val + 1 ∧ id_row_ok_loop c co i w b' j' = ok r ∧
        (b' = true → ok1 = true ∧
          gs c (co.val + i.val * w.val + j.val) = if i.val = j.val then 1 else 0) := by
  intro ok1 j r hj h
  rw [id_row_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hj)] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨j1, hj1, h⟩ := bind_eq_ok h
  refine ⟨_, j1, add_ok hj1, h, fun hb => ?_⟩
  obtain ⟨hb1, heq⟩ := and_dec hb
  refine ⟨hb1, ?_⟩
  have hv : (i5.val : ZP) = (i6.val : ZP) := by rw [heq]
  rw [(ok_inj hi5).symm, cast64, (index_ok hi4).2, add_ok hi3, add_ok hi2, mul_ok hi1,
    (ok_inj hi6).symm, fromBool_val] at hv
  rw [gs, hv]
  by_cases e : i.val = j.val
  · rw [if_pos (usz_eq.2 e), if_pos e]
  · rw [if_neg (fun h' => e (usz_eq.1 h')), if_neg e]

theorem id_row_spec {c : Slice U32} {co i w : Usize} (h : id_row_ok c co i w = ok true) :
    ∀ j, j < w.val → gs c (co.val + i.val * w.val + j) = if i.val = j then 1 else 0 :=
  flag_loop0 (F := fun ok1 j => id_row_ok_loop c co i w ok1 j)
    (id_row_loop_stop c co i w) (id_row_loop_step c co i w) h

theorem id_loop_stop (c : Slice U32) (co w : Usize) :
    ∀ (ok1 : Bool) (i : Usize), ¬ i.val < w.val → id_ok_loop c co w ok1 i = ok ok1 := by
  intro ok1 i hi
  rw [id_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hi)]

theorem id_loop_step (c : Slice U32) (co w : Usize) :
    ∀ (ok1 : Bool) (i : Usize) (r : Bool), i.val < w.val →
      id_ok_loop c co w ok1 i = ok r →
      ∃ b' i', i'.val = i.val + 1 ∧ id_ok_loop c co w b' i' = ok r ∧
        (b' = true → ok1 = true ∧ ∀ j, j < w.val →
          gs c (co.val + i.val * w.val + j) = if i.val = j then 1 else 0) := by
  intro ok1 i r hi h
  rw [id_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hi)] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  refine ⟨_, i1, add_ok hi1, h, fun hb => ?_⟩
  obtain ⟨hok, hb1t⟩ := and_true' hb
  exact ⟨hok, id_row_spec (hb1t ▸ hb1)⟩

/-- `id_ok`: the block is the identity. -/
theorem id_spec {c : Slice U32} {co w : Usize} (h : id_ok c co w = ok true) :
    ∀ i, i < w.val → ∀ j, j < w.val → gs c (co.val + i * w.val + j) = if i = j then 1 else 0 :=
  flag_loop0 (F := fun ok1 i => id_ok_loop c co w ok1 i) (id_loop_stop c co w) (id_loop_step c co w) h

theorem ech_row_loop_stop (e : Slice U32) (n : Usize) (lst : Slice U32) (a r : Usize) :
    ∀ (ok1 : Bool) (b : Usize), ¬ b.val < r.val → ech_row_ok_loop e n lst a r ok1 b = ok ok1 := by
  intro ok1 b hb
  rw [ech_row_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hb)]

theorem ech_row_loop_step (e : Slice U32) (n : Usize) (lst : Slice U32) (a r : Usize) :
    ∀ (ok1 : Bool) (b : Usize) (res : Bool), b.val < r.val →
      ech_row_ok_loop e n lst a r ok1 b = ok res →
      ∃ b' bb, bb.val = b.val + 1 ∧ ech_row_ok_loop e n lst a r b' bb = ok res ∧
        (b' = true → ok1 = true ∧
          gs e (a.val * n.val + gi lst b.val) = if a.val = b.val then 1 else 0) := by
  intro ok1 b res hb h
  rw [ech_row_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hb)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  refine ⟨_, b1, add_ok hb1, h, fun hb' => ?_⟩
  obtain ⟨hok, heq⟩ := and_dec hb'
  refine ⟨hok, ?_⟩
  have hv : (i5.val : ZP) = (i6.val : ZP) := by rw [heq]
  rw [(ok_inj hi5).symm, cast64, (index_ok hi4).2, add_ok hi3, mul_ok hi, (ok_inj hi2).symm, castUs,
    (index_ok hi1).2, (ok_inj hi6).symm, fromBool_val] at hv
  rw [gs, gi, hv]
  by_cases e' : a.val = b.val
  · rw [if_pos (usz_eq.2 e'), if_pos e']
  · rw [if_neg (fun h' => e' (usz_eq.1 h')), if_neg e']

theorem ech_row_spec {e lst : Slice U32} {n a r : Usize} (h : ech_row_ok e n lst a r = ok true) :
    ∀ b, b < r.val → gs e (a.val * n.val + gi lst b) = if a.val = b then 1 else 0 :=
  flag_loop0 (F := fun ok1 b => ech_row_ok_loop e n lst a r ok1 b)
    (ech_row_loop_stop e n lst a r) (ech_row_loop_step e n lst a r) h

theorem ech_loop_stop (e : Slice U32) (n : Usize) (lst : Slice U32) (r : Usize) :
    ∀ (ok1 : Bool) (a : Usize), ¬ a.val < r.val → ech_ok_loop e n lst r ok1 a = ok ok1 := by
  intro ok1 a ha
  rw [ech_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact ha)]

theorem ech_loop_step (e : Slice U32) (n : Usize) (lst : Slice U32) (r : Usize) :
    ∀ (ok1 : Bool) (a : Usize) (res : Bool), a.val < r.val →
      ech_ok_loop e n lst r ok1 a = ok res →
      ∃ b' a', a'.val = a.val + 1 ∧ ech_ok_loop e n lst r b' a' = ok res ∧
        (b' = true → ok1 = true ∧ ∀ b, b < r.val →
          gs e (a.val * n.val + gi lst b) = if a.val = b then 1 else 0) := by
  intro ok1 a res ha h
  rw [ech_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact ha)] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  refine ⟨_, a1, add_ok ha1, h, fun hb => ?_⟩
  obtain ⟨hok, hb1t⟩ := and_true' hb
  exact ⟨hok, ech_row_spec (hb1t ▸ hb1)⟩

/-- `ech_ok`: `E` is the identity on the pivot columns `lst[0..r)`. -/
theorem ech_spec {e lst : Slice U32} {n r : Usize} (h : ech_ok e n lst r = ok true) :
    ∀ a, a < r.val → ∀ b, b < r.val → gs e (a * n.val + gi lst b) = if a = b then 1 else 0 :=
  flag_loop0 (F := fun ok1 a => ech_ok_loop e n lst r ok1 a) (ech_loop_stop e n lst r)
    (ech_loop_step e n lst r) h

theorem perm_left_loop_stop (lst tag : Slice U32) (n : Usize) :
    ∀ (ok1 : Bool) (x : Usize), ¬ x.val < n.val → perm_left_ok_loop lst tag n ok1 x = ok ok1 := by
  intro ok1 x hx
  rw [perm_left_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hx)]

theorem perm_left_loop_step (lst tag : Slice U32) (n : Usize) :
    ∀ (ok1 : Bool) (x : Usize) (res : Bool), x.val < n.val →
      perm_left_ok_loop lst tag n ok1 x = ok res →
      ∃ b' x', x'.val = x.val + 1 ∧ perm_left_ok_loop lst tag n b' x' = ok res ∧
        (b' = true → ok1 = true ∧ (gi lst x.val < tag.val.length ∧ gi tag (gi lst x.val) = x.val)) := by
  intro ok1 x res hx h
  rw [perm_left_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hx)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨x1, hx1, h⟩ := bind_eq_ok h
  refine ⟨_, x1, add_ok hx1, h, fun hb => ?_⟩
  obtain ⟨hok, heq⟩ := and_dec hb
  have e1 : i1.val = gi lst x.val := by rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
  refine ⟨hok, e1 ▸ (index_ok hi2).1, ?_⟩
  have hv : i3.val = i4.val := by rw [heq]
  rw [(ok_inj hi3).symm, cast64, (index_ok hi2).2, (ok_inj hi4).symm, castUs64, e1] at hv
  exact hv

theorem perm_left_spec {lst tag : Slice U32} {n : Usize} (h : perm_left_ok lst tag n = ok true) :
    ∀ x, x < n.val → gi lst x < tag.val.length ∧ gi tag (gi lst x) = x :=
  flag_loop0 (F := fun ok1 x => perm_left_ok_loop lst tag n ok1 x) (perm_left_loop_stop lst tag n)
    (perm_left_loop_step lst tag n) h

theorem perm_right_loop_stop (lst tag : Slice U32) (n : Usize) :
    ∀ (ok1 : Bool) (c : Usize), ¬ c.val < n.val → perm_right_ok_loop lst tag n ok1 c = ok ok1 := by
  intro ok1 c hc
  rw [perm_right_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hc)]

theorem perm_right_loop_step (lst tag : Slice U32) (n : Usize) :
    ∀ (ok1 : Bool) (c : Usize) (res : Bool), c.val < n.val →
      perm_right_ok_loop lst tag n ok1 c = ok res →
      ∃ b' c', c'.val = c.val + 1 ∧ perm_right_ok_loop lst tag n b' c' = ok res ∧
        (b' = true → ok1 = true ∧ (gi tag c.val < lst.val.length ∧ gi lst (gi tag c.val) = c.val)) := by
  intro ok1 c res hc h
  rw [perm_right_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hc)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨c1, hc1, h⟩ := bind_eq_ok h
  refine ⟨_, c1, add_ok hc1, h, fun hb => ?_⟩
  obtain ⟨hok, heq⟩ := and_dec hb
  have e1 : i1.val = gi tag c.val := by rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
  refine ⟨hok, e1 ▸ (index_ok hi2).1, ?_⟩
  have hv : i3.val = i4.val := by rw [heq]
  rw [(ok_inj hi3).symm, cast64, (index_ok hi2).2, (ok_inj hi4).symm, castUs64, e1] at hv
  exact hv

theorem perm_right_spec {lst tag : Slice U32} {n : Usize} (h : perm_right_ok lst tag n = ok true) :
    ∀ c, c < n.val → gi tag c < lst.val.length ∧ gi lst (gi tag c) = c :=
  flag_loop0 (F := fun ok1 c => perm_right_ok_loop lst tag n ok1 c) (perm_right_loop_stop lst tag n)
    (perm_right_loop_step lst tag n) h

theorem nvec_row_loop_stop (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) :
    ∀ (ok1 : Bool) (t : Usize), ¬ t.val < n.val → nvec_row_ok_loop nm e n tag r f ff ok1 t = ok ok1 := by
  intro ok1 t ht
  rw [nvec_row_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact ht)]

/-- The n_f value at column `t`. -/
def nval (e : Slice U32) (n : ℕ) (tag : Slice U32) (r ff t : ℕ) : ZP :=
  (if t = ff then 1 else 0) - (if gi tag t < r then gs e (gi tag t * n + ff) else 0)

theorem nvec_row_loop_step (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) :
    ∀ (ok1 : Bool) (t : Usize) (res : Bool), t.val < n.val →
      nvec_row_ok_loop nm e n tag r f ff ok1 t = ok res →
      ∃ b' t', t'.val = t.val + 1 ∧ nvec_row_ok_loop nm e n tag r f ff b' t' = ok res ∧
        (b' = true → ok1 = true ∧ gs nm (f.val * n.val + t.val) = nval e n.val tag r.val ff.val t.val) := by
  intro ok1 t res ht h
  rw [nvec_row_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact ht)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨g, hg, h⟩ := bind_eq_ok h
  obtain ⟨isf, hisf, h⟩ := bind_eq_ok h
  obtain ⟨ip, hip, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨ev, hev, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨want, hwant, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  obtain ⟨i10, hi10, h⟩ := bind_eq_ok h
  obtain ⟨i11, hi11, h⟩ := bind_eq_ok h
  obtain ⟨i12, hi12, h⟩ := bind_eq_ok h
  obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
  refine ⟨_, t1, add_ok ht1, h, fun hb => ?_⟩
  obtain ⟨hok, heq⟩ := and_dec hb
  refine ⟨hok, ?_⟩
  have eg : g.val = gi tag t.val := by rw [(ok_inj hg).symm, castUs, (index_ok hi).2]; rfl
  have hv : (i12.val : ZP) = (want.val : ZP) := by rw [heq]
  obtain ⟨s8, hle⟩ := sub_ok hi8
  rw [(ok_inj hi12).symm, cast64, (index_ok hi11).2, add_ok hi10, mul_ok hi9, (modP_lt hwant).2, s8,
    Nat.cast_sub hle, add_ok hi6, mul_ok hi7, Nat.cast_add, Nat.cast_mul, P_val,
    (ok_inj hisf).symm, (ok_inj hip).symm, fromBool_val, fromBool_val] at hv
  rw [gs, hv, nval]
  have hP : ((PN : ℕ) : ZP) = 0 := ZMod.natCast_self PN
  rw [hP, add_zero]
  have eqt : ((if t = ff then (1 : ZP) else 0) = if t.val = ff.val then 1 else 0) := by
    by_cases et : t.val = ff.val
    · rw [if_pos (usz_eq.2 et), if_pos et]
    · rw [if_neg (fun h' => et (usz_eq.1 h')), if_neg et]
  rw [eqt]
  by_cases eg' : g.val < r.val
  · have hr : r.val ≠ 0 := by omega
    have e1 : i1.val = g.val := by rw [rem_ok hr hi1]; exact Nat.mod_eq_of_lt eg'
    have hevv : (ev.val : ZP) = gs e (gi tag t.val * n.val + ff.val) := by
      rw [(modP_lt hev).2, (ok_inj hi5).symm, cast64, (index_ok hi4).2, add_ok hi3, mul_ok hi2, e1, eg]
      rfl
    rw [hevv, if_pos (show g < r from (UScalar.lt_equiv g r).2 eg'),
      if_pos (show gi tag t.val < r.val by rw [← eg]; exact eg'), one_mul]
  · rw [if_neg (show ¬ g < r from fun h' => eg' ((UScalar.lt_equiv g r).1 h')),
      if_neg (show ¬ gi tag t.val < r.val by rw [← eg]; exact eg'), zero_mul]

theorem nvec_row_spec {nm e tag : Slice U32} {n r f ff : Usize}
    (h : nvec_row_ok nm e n tag r f ff = ok true) :
    ∀ t, t < n.val → gs nm (f.val * n.val + t) = nval e n.val tag r.val ff.val t :=
  flag_loop0 (F := fun ok1 t => nvec_row_ok_loop nm e n tag r f ff ok1 t)
    (nvec_row_loop_stop nm e n tag r f ff) (nvec_row_loop_step nm e n tag r f ff) h

theorem nvec_loop_stop (nm e : Slice U32) (n : Usize) (lst tag : Slice U32) (r k : Usize) :
    ∀ (ok1 : Bool) (f : Usize), ¬ f.val < k.val → nvec_ok_loop nm e n lst tag r k ok1 f = ok ok1 := by
  intro ok1 f hf
  rw [nvec_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hf)]

theorem nvec_loop_step (nm e : Slice U32) (n : Usize) (lst tag : Slice U32) (r k : Usize) :
    ∀ (ok1 : Bool) (f : Usize) (res : Bool), f.val < k.val →
      nvec_ok_loop nm e n lst tag r k ok1 f = ok res →
      ∃ b' f', f'.val = f.val + 1 ∧ nvec_ok_loop nm e n lst tag r k b' f' = ok res ∧
        (b' = true → ok1 = true ∧ ∀ t, t < n.val →
          gs nm (f.val * n.val + t) = nval e n.val tag r.val (gi lst (r.val + f.val)) t) := by
  intro ok1 f res hf h
  rw [nvec_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hf)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨ff, hff, h⟩ := bind_eq_ok h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  obtain ⟨f1, hf1, h⟩ := bind_eq_ok h
  refine ⟨_, f1, add_ok hf1, h, fun hb => ?_⟩
  obtain ⟨hok, hb1t⟩ := and_true' hb
  have eff : ff.val = gi lst (r.val + f.val) := by
    rw [(ok_inj hff).symm, castUs, (index_ok hi1).2, add_ok hi]; rfl
  refine ⟨hok, fun t ht => ?_⟩
  rw [← eff]
  exact nvec_row_spec (hb1t ▸ hb1) t ht

/-- `nvec_ok`: the supplied `n_f` matrix, free column `f` at `lst[r+f]`. -/
theorem nvec_spec {nm e lst tag : Slice U32} {n r k : Usize}
    (h : nvec_ok nm e n lst tag r k = ok true) :
    ∀ f, f < k.val → ∀ t, t < n.val →
      gs nm (f * n.val + t) = nval e n.val tag r.val (gi lst (r.val + f)) t :=
  flag_loop0 (F := fun ok1 f => nvec_ok_loop nm e n lst tag r k ok1 f)
    (nvec_loop_stop nm e n lst tag r k) (nvec_loop_step nm e n lst tag r k) h

/-- What `lifts_ok` certifies about lift `l`. -/
def LiftOK (o u id lw loff : Slice U32) (l : ℕ) : Prop :=
  (∀ i, i < gi lw l → ∀ j, j < gi lw l →
    ∑ p ∈ Finset.range (gi lw l), gs o (gi loff l + i * gi lw l + p) * gs u (gi loff l + j + p * gi lw l)
      = gs id (gi loff l + i * gi lw l + j)) ∧
  (∀ i, i < gi lw l → ∀ j, j < gi lw l → gs id (gi loff l + i * gi lw l + j) = if i = j then 1 else 0)

theorem lifts_loop_stop (o u id lw loff : Slice U32) (nl : Usize) :
    ∀ (ok1 : Bool) (l : Usize), ¬ l.val < nl.val → lifts_ok_loop o u id lw loff nl ok1 l = ok ok1 := by
  intro ok1 l hl
  rw [lifts_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hl)]

theorem lifts_loop_step (o u id lw loff : Slice U32) (nl : Usize) :
    ∀ (ok1 : Bool) (l : Usize) (res : Bool), l.val < nl.val →
      lifts_ok_loop o u id lw loff nl ok1 l = ok res →
      ∃ b' l', l'.val = l.val + 1 ∧ lifts_ok_loop o u id lw loff nl b' l' = ok res ∧
        (b' = true → ok1 = true ∧ LiftOK o u id lw loff l.val) := by
  intro ok1 l res hl h
  rw [lifts_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hl)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨w, hw, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨off, hoff, h⟩ := bind_eq_ok h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  obtain ⟨l1, hl1, h⟩ := bind_eq_ok h
  refine ⟨_, l1, add_ok hl1, h, fun hb => ?_⟩
  obtain ⟨hb', hb1t⟩ := and_true' hb
  obtain ⟨hok, hb0t⟩ := and_true' hb'
  have ew : w.val = gi lw l.val := by rw [(ok_inj hw).symm, castUs, (index_ok hi).2]; rfl
  have eo : off.val = gi loff l.val := by rw [(ok_inj hoff).symm, castUs, (index_ok hi1).2]; rfl
  have hp := prod_spec (hb0t ▸ hb0)
  have hid := id_spec (hb1t ▸ hb1)
  rw [ew, eo] at hp hid
  exact ⟨hok, hp, hid⟩

/-- `lifts_ok`: every lift block satisfies `LiftOK`. -/
theorem lifts_spec {o u id lw loff : Slice U32} {nl : Usize} (h : lifts_ok o u id lw loff nl = ok true) :
    ∀ l, l < nl.val → LiftOK o u id lw loff l :=
  flag_loop0 (F := fun ok1 l => lifts_ok_loop o u id lw loff nl ok1 l)
    (lifts_loop_stop o u id lw loff nl) (lifts_loop_step o u id lw loff nl) h

#print axioms prod_spec
#print axioms id_spec
#print axioms ech_spec
#print axioms perm_left_spec
#print axioms perm_right_spec
#print axioms nvec_spec
#print axioms lifts_spec

end R1Z.CertCheck
