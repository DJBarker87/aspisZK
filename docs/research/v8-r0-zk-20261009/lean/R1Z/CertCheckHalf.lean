import R1Z.CertCheckBase
import Mathlib.Tactic.LinearCombination

/-! D49.4 C3: the extracted HalfOK test.  `half_ok a h = ok true` gives the four
limb equations of `(α₉ - 1/2)·h = 1` in QM31 = CM31[u]/(u² - (2+i)), CM31 =
M31[i]/(i² + 1), limbs (c0.a, c0.b, c1.a, c1.b); `1/2 = 2^30 = 1073741824` in M31. -/

set_option autoImplicit false

namespace R1Z.CertCheck
open Aeneas Aeneas.Std Result R1CertCheck

theorem add_z {ty : UScalarTy} {x y z : UScalar ty} (h : x + y = ok z) :
    (z.val : ZP) = (x.val : ZP) + (y.val : ZP) := by
  rw [add_ok h, Nat.cast_add]

theorem mul_z {ty : UScalarTy} {x y z : UScalar ty} (h : x * y = ok z) :
    (z.val : ZP) = (x.val : ZP) * (y.val : ZP) := by
  rw [mul_ok h, Nat.cast_mul]

theorem sub_z {ty : UScalarTy} {x y z : UScalar ty} (h : x - y = ok z) :
    (z.val : ZP) = (x.val : ZP) - (y.val : ZP) := by
  obtain ⟨e, hle⟩ := sub_ok h
  rw [e, Nat.cast_sub hle]

theorem mm_z {x y : U32} {z : U64} (h : mm x y = ok z) : (z.val : ZP) = (x.val : ZP) * (y.val : ZP) := by
  unfold mm at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  rw [(modP_lt h).2, mul_z hi2, (ok_inj hi).symm, (ok_inj hi1).symm, cast64, cast64]

theorem PZ : ((P.val : ℕ) : ZP) = 0 := by rw [P_val]; exact ZMod.natCast_self PN

theorem idx_z {v : Slice U32} {i : Usize} {x : U32} (h : Slice.index_usize v i = ok x) :
    (x.val : ZP) = gs v i.val := by
  rw [(index_ok h).2]; rfl

/-- The four HalfOK limb equations (`x0 = α₉.c0.a - 1/2`). -/
def HalfEq (a h : Slice U32) : Prop :=
  ((gs a 0 - 1073741824) * gs h 0 - gs a 1 * gs h 1 + 2 * (gs a 2 * gs h 2 - gs a 3 * gs h 3)
      - (gs a 2 * gs h 3 + gs a 3 * gs h 2) = 1) ∧
  ((gs a 0 - 1073741824) * gs h 1 + gs a 1 * gs h 0 + (gs a 2 * gs h 2 - gs a 3 * gs h 3)
      + 2 * (gs a 2 * gs h 3 + gs a 3 * gs h 2) = 0) ∧
  ((gs a 0 - 1073741824) * gs h 2 - gs a 1 * gs h 3 + gs a 2 * gs h 0 - gs a 3 * gs h 1 = 0) ∧
  ((gs a 0 - 1073741824) * gs h 3 + gs a 1 * gs h 2 + gs a 2 * gs h 1 + gs a 3 * gs h 0 = 0)

theorem u0 : (0#usize : Usize).val = 0 := by simp
theorem u1 : (1#usize : Usize).val = 1 := by simp
theorem u2 : (2#usize : Usize).val = 2 := by simp
theorem u3 : (3#usize : Usize).val = 3 := by simp
theorem two64 : (((2#u64 : U64).val : ℕ) : ZP) = 2 := by simp
theorem c64 : (((1073741824#u64 : U64).val : ℕ) : ZP) = 1073741824 := by simp
theorem one64 {x : U64} (h : x = 1#u64) : (x.val : ZP) = 1 := by rw [h]; simp
theorem zero64 {x : U64} (h : x = 0#u64) : (x.val : ZP) = 0 := by rw [h]; simp

theorem half_spec {a h : Slice U32} (hc : half_ok a h = ok true) : HalfEq a h := by
  unfold half_ok at hc
  obtain ⟨i, hi, hc⟩ := bind_eq_ok hc
  obtain ⟨i1, hi1, hc⟩ := bind_eq_ok hc
  obtain ⟨i2, hi2, hc⟩ := bind_eq_ok hc
  obtain ⟨i3, hi3, hc⟩ := bind_eq_ok hc
  obtain ⟨i4, hi4, hc⟩ := bind_eq_ok hc
  obtain ⟨x0, hx0, hc⟩ := bind_eq_ok hc
  obtain ⟨x01, hx01, hc⟩ := bind_eq_ok hc
  obtain ⟨x1, hx1, hc⟩ := bind_eq_ok hc
  obtain ⟨x2, hx2, hc⟩ := bind_eq_ok hc
  obtain ⟨x3, hx3, hc⟩ := bind_eq_ok hc
  obtain ⟨y0, hy0, hc⟩ := bind_eq_ok hc
  obtain ⟨y1, hy1, hc⟩ := bind_eq_ok hc
  obtain ⟨y2, hy2, hc⟩ := bind_eq_ok hc
  obtain ⟨y3, hy3, hc⟩ := bind_eq_ok hc
  obtain ⟨i5, hi5, hc⟩ := bind_eq_ok hc
  obtain ⟨i6, hi6, hc⟩ := bind_eq_ok hc
  obtain ⟨i7, hi7, hc⟩ := bind_eq_ok hc
  obtain ⟨i8, hi8, hc⟩ := bind_eq_ok hc
  obtain ⟨p, hp, hc⟩ := bind_eq_ok hc
  obtain ⟨i9, hi9, hc⟩ := bind_eq_ok hc
  obtain ⟨i10, hi10, hc⟩ := bind_eq_ok hc
  obtain ⟨i11, hi11, hc⟩ := bind_eq_ok hc
  obtain ⟨q, hq, hc⟩ := bind_eq_ok hc
  obtain ⟨i12, hi12, hc⟩ := bind_eq_ok hc
  obtain ⟨i13, hi13, hc⟩ := bind_eq_ok hc
  obtain ⟨i14, hi14, hc⟩ := bind_eq_ok hc
  obtain ⟨i15, hi15, hc⟩ := bind_eq_ok hc
  obtain ⟨i16, hi16, hc⟩ := bind_eq_ok hc
  obtain ⟨i17, hi17, hc⟩ := bind_eq_ok hc
  obtain ⟨i18, hi18, hc⟩ := bind_eq_ok hc
  obtain ⟨i19, hi19, hc⟩ := bind_eq_ok hc
  obtain ⟨r0, hr0, hc⟩ := bind_eq_ok hc
  obtain ⟨i20, hi20, hc⟩ := bind_eq_ok hc
  obtain ⟨i21, hi21, hc⟩ := bind_eq_ok hc
  obtain ⟨i22, hi22, hc⟩ := bind_eq_ok hc
  obtain ⟨i23, hi23, hc⟩ := bind_eq_ok hc
  obtain ⟨i24, hi24, hc⟩ := bind_eq_ok hc
  obtain ⟨i25, hi25, hc⟩ := bind_eq_ok hc
  obtain ⟨r1, hr1, hc⟩ := bind_eq_ok hc
  obtain ⟨i26, hi26, hc⟩ := bind_eq_ok hc
  obtain ⟨i27, hi27, hc⟩ := bind_eq_ok hc
  obtain ⟨i28, hi28, hc⟩ := bind_eq_ok hc
  obtain ⟨i29, hi29, hc⟩ := bind_eq_ok hc
  obtain ⟨i30, hi30, hc⟩ := bind_eq_ok hc
  obtain ⟨i31, hi31, hc⟩ := bind_eq_ok hc
  obtain ⟨i32, hi32, hc⟩ := bind_eq_ok hc
  obtain ⟨i33, hi33, hc⟩ := bind_eq_ok hc
  obtain ⟨i34, hi34, hc⟩ := bind_eq_ok hc
  obtain ⟨r2, hr2, hc⟩ := bind_eq_ok hc
  obtain ⟨i35, hi35, hc⟩ := bind_eq_ok hc
  obtain ⟨i36, hi36, hc⟩ := bind_eq_ok hc
  obtain ⟨i37, hi37, hc⟩ := bind_eq_ok hc
  obtain ⟨i38, hi38, hc⟩ := bind_eq_ok hc
  obtain ⟨i39, hi39, hc⟩ := bind_eq_ok hc
  obtain ⟨i40, hi40, hc⟩ := bind_eq_ok hc
  obtain ⟨i41, hi41, hc⟩ := bind_eq_ok hc
  obtain ⟨r3, hr3, hc⟩ := bind_eq_ok hc
  have hb := ok_inj hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩ := hb
  have hx0lt : x0.val < 2 ^ 32 := lt_trans (modP_lt hx0).1 (by norm_num)
  have ex0 : (x01.val : ZP) = gs a 0 - 1073741824 := by
    rw [(ok_inj hx01).symm, cast32 x0 hx0lt, (modP_lt hx0).2, sub_z hi4, add_z hi3, PZ,
      (modP_lt hi2).2, (ok_inj hi1).symm, cast64, idx_z hi, u0, c64, add_zero]
  have E0 := one64 e0
  rw [(modP_lt hr0).2, sub_z hi19, add_z hi18, add_z hi17, mul_z hi16, sub_z hi15, add_z hi13,
    mm_z hi12, mm_z hi14, (modP_lt hq).2, add_z hi11, mm_z hi9, mm_z hi10, (modP_lt hp).2,
    sub_z hi8, add_z hi6, mm_z hi5, mm_z hi7, PZ, ex0, idx_z hx1, idx_z hx2, idx_z hx3,
    idx_z hy0, idx_z hy1, idx_z hy2, idx_z hy3, u0, u1, u2, u3, two64] at E0
  have E1 := zero64 e1
  rw [(modP_lt hr1).2, add_z hi25, add_z hi23, mul_z hi24, add_z hi22, mm_z hi20, mm_z hi21,
    (modP_lt hq).2, add_z hi11, mm_z hi9, mm_z hi10, (modP_lt hp).2, sub_z hi8, add_z hi6,
    mm_z hi5, mm_z hi7, PZ, ex0, idx_z hx1, idx_z hx2, idx_z hx3, idx_z hy0, idx_z hy1,
    idx_z hy2, idx_z hy3, u0, u1, u2, u3, two64] at E1
  have E2 := zero64 e2
  rw [(modP_lt hr2).2, sub_z hi34, add_z hi32, add_z hi31, sub_z hi29, add_z hi27, mm_z hi26,
    mm_z hi28, mm_z hi30, mm_z hi33, PZ, ex0, idx_z hx1, idx_z hx2, idx_z hx3, idx_z hy0,
    idx_z hy1, idx_z hy2, idx_z hy3, u0, u1, u2, u3] at E2
  have E3 := zero64 e3
  rw [(modP_lt hr3).2, add_z hi41, add_z hi39, add_z hi37, mm_z hi35, mm_z hi36, mm_z hi38,
    mm_z hi40, ex0, idx_z hx1, idx_z hx2, idx_z hx3, idx_z hy0, idx_z hy1, idx_z hy2,
    idx_z hy3, u0, u1, u2, u3] at E3
  exact ⟨by linear_combination E0, by linear_combination E1, by linear_combination E2,
    by linear_combination E3⟩

#print axioms mm_z
#print axioms half_spec

end R1Z.CertCheck
