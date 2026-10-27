import R1Z.CertCheckBase

/-! D49.4 C3: the extracted dot products.  `dot` is the strided product
`∑_{p<n} a[ao + p·ast] · b[bo + p·bst]` over M31 and `kdot` the gathered one
`∑_{p<n} m[idx[io+p]·st + i] · c[co + p]` (the pivot part of `kcoord`).  Both
results are canonical (`< P`). -/

set_option autoImplicit false

namespace R1Z.CertCheck
open Aeneas Aeneas.Std Result R1CertCheck
open scoped BigOperators

/-- The natural value of a slice entry (indices). -/
def gi (s : Slice U32) (k : ℕ) : ℕ := (s.val[k]!).val

theorem gs_eq (s : Slice U32) (k : ℕ) : gs s k = (gi s k : ZP) := rfl

theorem dot_loop_stop (a : Slice U32) (ao ast : Usize) (b : Slice U32) (bo bst n : Usize) :
    ∀ (acc : U64) (p : Usize), ¬ p.val < n.val → dot_loop a ao ast b bo bst n acc p = ok acc := by
  intro acc p hp
  rw [dot_loop, if_neg (by rw [UScalar.lt_equiv]; exact hp)]

theorem dot_loop_step (a : Slice U32) (ao ast : Usize) (b : Slice U32) (bo bst n : Usize) :
    ∀ (acc : U64) (p : Usize) (r : U64), p.val < n.val →
      dot_loop a ao ast b bo bst n acc p = ok r →
      ∃ acc' p', p'.val = p.val + 1 ∧ dot_loop a ao ast b bo bst n acc' p' = ok r ∧
        (acc'.val : ZP) = (acc.val : ZP) +
          gs a (ao.val + p.val * ast.val) * gs b (bo.val + p.val * bst.val) := by
  intro acc p r hp h
  rw [dot_loop, if_pos (by rw [UScalar.lt_equiv]; exact hp)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨x, hx, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨y, hy, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨acc1, hacc, h⟩ := bind_eq_ok h
  obtain ⟨p1, hp1, h⟩ := bind_eq_ok h
  refine ⟨acc1, p1, add_ok hp1, h, ?_⟩
  have ex : x = UScalar.cast .U64 i2 := (ok_inj hx).symm
  have ey : y = UScalar.cast .U64 i5 := (ok_inj hy).symm
  rw [add_ok hacc, Nat.cast_add, (modP_lt hi7).2, mul_ok hi6, Nat.cast_mul, ex, ey, cast64,
    cast64, (index_ok hi2).2, (index_ok hi5).2, add_ok hi1, add_ok hi4, mul_ok hi, mul_ok hi3]
  rfl

/-- `dot` computes the strided M31 product. -/
theorem dot_spec {a b : Slice U32} {ao ast bo bst n : Usize} {r : U64}
    (h : dot a ao ast b bo bst n = ok r) :
    r.val < PN ∧ (r.val : ZP) =
      ∑ p ∈ Finset.range n.val, gs a (ao.val + p * ast.val) * gs b (bo.val + p * bst.val) := by
  unfold dot at h
  obtain ⟨acc, hacc, h⟩ := bind_eq_ok h
  have e := acc_loop0 (F := fun acc p => dot_loop a ao ast b bo bst n acc p) (n := n.val)
    (T := fun p => gs a (ao.val + p * ast.val) * gs b (bo.val + p * bst.val))
    (dot_loop_stop a ao ast b bo bst n) (dot_loop_step a ao ast b bo bst n) hacc
  obtain ⟨hlt, hv⟩ := modP_lt h
  exact ⟨hlt, hv.trans e⟩

theorem kdot_loop_stop (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co n : Usize) :
    ∀ (acc : U64) (p : Usize), ¬ p.val < n.val → kdot_loop m st i idx io c co n acc p = ok acc := by
  intro acc p hp
  rw [kdot_loop, if_neg (by rw [UScalar.lt_equiv]; exact hp)]

theorem kdot_loop_step (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co n : Usize) :
    ∀ (acc : U64) (p : Usize) (r : U64), p.val < n.val →
      kdot_loop m st i idx io c co n acc p = ok r →
      ∃ acc' p', p'.val = p.val + 1 ∧ kdot_loop m st i idx io c co n acc' p' = ok r ∧
        (acc'.val : ZP) = (acc.val : ZP) +
          gs m (gi idx (io.val + p.val) * st.val + i.val) * gs c (co.val + p.val) := by
  intro acc p r hp h
  rw [kdot_loop, if_pos (by rw [UScalar.lt_equiv]; exact hp)] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨t, ht, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨x, hx, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨y, hy, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  obtain ⟨acc1, hacc, h⟩ := bind_eq_ok h
  obtain ⟨p1, hp1, h⟩ := bind_eq_ok h
  refine ⟨acc1, p1, add_ok hp1, h, ?_⟩
  have et : t = UScalar.cast .Usize i2 := (ok_inj ht).symm
  have ex : x = UScalar.cast .U64 i5 := (ok_inj hx).symm
  have ey : y = UScalar.cast .U64 i7 := (ok_inj hy).symm
  rw [add_ok hacc, Nat.cast_add, (modP_lt hi9).2, mul_ok hi8, Nat.cast_mul, ex, ey, cast64,
    cast64, (index_ok hi5).2, (index_ok hi7).2, add_ok hi4, mul_ok hi3, et, castUs,
    (index_ok hi2).2, add_ok hi1, add_ok hi6]
  rfl

/-- `kdot` computes the gathered M31 product. -/
theorem kdot_spec {m idx c : Slice U32} {st i io co n : Usize} {r : U64}
    (h : kdot m st i idx io c co n = ok r) :
    r.val < PN ∧ (r.val : ZP) =
      ∑ p ∈ Finset.range n.val, gs m (gi idx (io.val + p) * st.val + i.val) * gs c (co.val + p) := by
  unfold kdot at h
  obtain ⟨acc, hacc, h⟩ := bind_eq_ok h
  have e := acc_loop0 (F := fun acc p => kdot_loop m st i idx io c co n acc p) (n := n.val)
    (T := fun p => gs m (gi idx (io.val + p) * st.val + i.val) * gs c (co.val + p))
    (kdot_loop_stop m st i idx io c co n) (kdot_loop_step m st i idx io c co n) hacc
  obtain ⟨hlt, hv⟩ := modP_lt h
  exact ⟨hlt, hv.trans e⟩

#print axioms dot_loop_step
#print axioms dot_spec
#print axioms kdot_loop_step
#print axioms kdot_spec

end R1Z.CertCheck
