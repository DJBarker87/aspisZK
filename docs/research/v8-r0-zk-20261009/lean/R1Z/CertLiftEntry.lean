import R1Z.CertLiftBasic
import R1Z.CertLiftFill

/-! D59.2 builder 2: the extracted lift entries as `K₄` limbs.  A C1 head entry is
limb `i mod 4` of an array whose `K₄` value is `headK … r (i/4)`; an opened entry is
limb 0 of `evK(sx, sy)` at the stored point; an entry is the row value minus the
inactive flag times the dependent row's (`c1_entry_spec`, `h1_entry_spec`). -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)
variable (al zz tr sx sy inact : Slice U32)

theorem aval {q : A4} {i : Usize} {v : U32} (h : Array.index_usize q i = ok v) :
    (v.val : ZP) = ga q i.val := by
  rw [aidx_ok h]; rfl

theorem c1_val_head (hT : Tower B) {r i : Usize} {v : U32} (hi : i.val < 24)
    (h : R1CertBuild.c1_val al zz tr sx sy r i = ok v) :
    ∃ q : A4, ψa B φ q = headK (Alimb B φ al) (Alimb B φ zz) (gN tr r.val) r.val (i.val / 4) ∧
      (v.val : ZP) = ga q (i.val % 4) := by
  unfold R1CertBuild.c1_val at h
  rw [if_pos (by rw [UScalar.lt_equiv]; simpa using hi)] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨q, hq, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  have four : (4#usize : Usize).val ≠ 0 := by simp
  refine ⟨q, ?_, ?_⟩
  · rw [head_q_spec B φ hT hq, div_ok four hi1]; simp
  · rw [aval h, rem_ok four hi2]; simp

theorem c1_val_open (hT : Tower B) {r i : Usize} {v : U32} (hi : 24 ≤ i.val)
    (h : R1CertBuild.c1_val al zz tr sx sy r i = ok v) :
    ∃ q : A4, ψa B φ q = evK (embR φ (gs sx (i.val - 24))) (embR φ (gs sy (i.val - 24))) (gN tr r.val) ∧
      (v.val : ZP) = ga q 0 := by
  unfold R1CertBuild.c1_val at h
  rw [if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨q, hq, h⟩ := bind_eq_ok h
  have e3 : i3.val = i.val - 24 := by rw [(sub_ok hi3).1]; simp
  refine ⟨q, ?_, ?_⟩
  · rw [evq_spec B φ hT hq, (qbase_spec B φ ha).1, (qbase_spec B φ ha1).1, idx_z' hi4, idx_z' hi5, e3,
      (ok_inj hi2).symm, castUs, (index_ok hi1).2]
    rfl
  · rw [aval h]; simp

theorem c1_entry_spec {r i : Usize} {v : U32} (h : R1CertBuild.c1_entry al zz tr sx sy inact r i = ok v) :
    ∃ o1 o2 : U32, R1CertBuild.c1_val al zz tr sx sy r i = ok o1 ∧
      R1CertBuild.c1_val al zz tr sx sy 1023#usize i = ok o2 ∧
      (v.val : ZP) = (o1.val : ZP) - gs inact r.val * (o2.val : ZP) := by
  unfold R1CertBuild.c1_entry at h
  obtain ⟨o1, h1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨o2, h2, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  refine ⟨o1, o2, h1, h2, ?_⟩
  rw [(fsub_spec h).2, (fmul_spec hi4).2, idx_z' hi2]

theorem tbq_spec {k : Usize} {z : A4} (h : R1CertBuild.tbq k = ok z) : ψa B φ z = tb B k.val := by
  unfold R1CertBuild.tbq at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3⟩ := make_ga i i1 i2 i3
  have cb : ∀ (w : U32) (lit : Usize) (n : ℕ), lit.val = n →
      lift (UScalar.cast_fromBool .U32 (decide (k = lit))) = ok w → (w.val : ZP) = if k.val = n then 1 else 0 := by
    intro w lit n hl hw
    rw [(ok_inj hw).symm, fromBool32Z]
    by_cases e : k.val = n
    · rw [if_pos ((ueq hl).2 e), if_pos e]
    · rw [if_neg (fun h' => e ((ueq hl).1 h')), if_neg e]
  rw [ψa, g0, g1, g2, g3, cb i 0#usize 0 (by simp) hi, cb i1 1#usize 1 (by simp) hi1,
    cb i2 2#usize 2 (by simp) hi2, cb i3 3#usize 3 (by simp) hi3]
  unfold ψ4 tb
  by_cases k0 : k.val = 0
  · simp [k0]
  by_cases k1 : k.val = 1
  · simp [k1]
  by_cases k2 : k.val = 2
  · simp [k2]
  by_cases k3 : k.val = 3
  · simp [k3]
  simp [k0, k1, k2, k3]

theorem h1_val_head (hT : Tower B) {r k i : Usize} {v : U32} (hi : i.val < 24)
    (h : R1CertBuild.h1_val al zz tr sx sy r k i = ok v) :
    ∃ q : A4, ψa B φ q = tb B k.val * headK (Alimb B φ al) (Alimb B φ zz) (gN tr r.val) r.val (i.val / 4) ∧
      (v.val : ZP) = ga q (i.val % 4) := by
  unfold R1CertBuild.h1_val at h
  rw [if_pos (by rw [UScalar.lt_equiv]; simpa using hi)] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨q, hq, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  have four : (4#usize : Usize).val ≠ 0 := by simp
  refine ⟨q, ?_, ?_⟩
  · rw [psi_qmul B φ hT hq, tbq_spec B φ ha, head_q_spec B φ hT ha1, div_ok four hi1]; simp
  · rw [aval h, rem_ok four hi2]; simp

theorem h1_val_open (hT : Tower B) {r k i : Usize} {v : U32} (hi : 24 ≤ i.val)
    (h : R1CertBuild.h1_val al zz tr sx sy r k i = ok v) :
    ∃ q : A4, ψa B φ q = tb B k.val *
        evK (embR φ (gs sx (4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4)))
          (embR φ (gs sy (4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4))) (gN tr r.val) ∧
      (v.val : ZP) = ga q ((i.val - 24) % 4) := by
  unfold R1CertBuild.h1_val at h
  rw [if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
  obtain ⟨m, hm, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨o, ho, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨vv, hvv, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨q, hq, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  have four : (4#usize : Usize).val ≠ 0 := by simp
  have sixteen : (16#usize : Usize).val ≠ 0 := by simp
  have em : m.val = i.val - 24 := by rw [(sub_ok hm).1]; simp
  have eo : o.val = 4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4 := by
    rw [add_ok ho, mul_ok hi2, div_ok sixteen hi1, div_ok four hi4, rem_ok sixteen hi3, em]; simp
  refine ⟨q, ?_, ?_⟩
  · rw [psi_qmul B φ hT hq, tbq_spec B φ ha2, evq_spec B φ hT hvv, (qbase_spec B φ ha).1,
      (qbase_spec B φ ha1).1, idx_z' hi7, idx_z' hi8, eo, (ok_inj hi6).symm, castUs, (index_ok hi5).2]
    rfl
  · rw [aval h, rem_ok four hi9, em]; simp

theorem h1_entry_spec {r k i : Usize} {v : U32}
    (h : R1CertBuild.h1_entry al zz tr sx sy inact r k i = ok v) :
    ∃ o1 o2 : U32, R1CertBuild.h1_val al zz tr sx sy r k i = ok o1 ∧
      R1CertBuild.h1_val al zz tr sx sy 0#usize k i = ok o2 ∧
      (v.val : ZP) = (o1.val : ZP) - gs inact r.val * (o2.val : ZP) := by
  unfold R1CertBuild.h1_entry at h
  obtain ⟨o1, h1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨o2, h2, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  refine ⟨o1, o2, h1, h2, ?_⟩
  rw [(fsub_spec h).2, (fmul_spec hi4).2, idx_z' hi2]

#print axioms c1_val_head
#print axioms c1_val_open
#print axioms c1_entry_spec
#print axioms tbq_spec
#print axioms h1_val_head
#print axioms h1_val_open
#print axioms h1_entry_spec

end R1Z.CertBuild
