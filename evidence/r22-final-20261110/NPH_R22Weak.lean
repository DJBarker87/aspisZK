import NPH_R22CM31

/-! NPH_ (R22 re-pin): the weak limb domain `limb ≤ P` (P = 2^31-1) is closed under every
M31/CM31 kernel of NPH_R22FieldRef/Copies/CM31 and every checked operation on it succeeds.
It is strictly larger than canonicality and covers the deliberately masked limbs
`M31(x & P)` of frozen field.rs (qm31_m31_dot rejection path), whose value can be P.
Statements: checked success, output limbs ≤ P, and for add/sub the R22 tree corollary. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Weak
open Aeneas Aeneas.Std Result AspisR1.R22TotalCheckedComposition AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22CM31

theorem cross_okw (l r : U64) (hl : l.val ≤ 4294967294) (hr : r.val ≤ 4294967294) :
    ∃ z, (l * r : Result U64) = ok z ∧ z.val = l.val * r.val := by
  have hm : l.val * r.val ≤ 4294967294 * 4294967294 := Nat.mul_le_mul hl hr
  exact mul_ok l r (by rw [max64]; omega)

theorem r23_totalw (l r : U64) (hl : l.val ≤ 4294967294) (hr : r.val ≤ 4294967294) :
    ∃ z, AspisR72Sampler.field.r23_product_u32_bounded l r = ok z ∧ z.val = l.val * r.val := by
  have hl32 := cast32_val l (by omega)
  have hr32 := cast32_val r (by omega)
  obtain ⟨z, hz, hv⟩ := cross_okw l r hl hr
  obtain ⟨z2, hz2, hv2⟩ := cross_okw (core.convert.num.FromU64U32.from (UScalar.cast .U32 l))
    (core.convert.num.FromU64U32.from (UScalar.cast .U32 r))
    (by rw [from_val, hl32]; exact hl) (by rw [from_val, hr32]; exact hr)
  unfold AspisR72Sampler.field.r23_product_u32_bounded
  by_cases c1 : l <= core.convert.num.FromU64U32.from core.num.U32.MAX
  · by_cases c2 : r <= core.convert.num.FromU64U32.from core.num.U32.MAX
    · refine ⟨z2, ?_, by rw [hv2, from_val, from_val, hl32, hr32]⟩
      simp only [lift, bind_tc_ok, c1, c2, ↓reduceIte, hz2]
    · refine ⟨z, ?_, hv⟩
      simp only [lift, bind_tc_ok, c1, c2, ↓reduceIte, hz]
  · refine ⟨z, ?_, hv⟩
    simp only [lift, bind_tc_ok, c1, ↓reduceIte, hz]

theorem refAdd_weak (x y : U32) (hx : x.val ≤ 2147483647) (hy : y.val ≤ 2147483647) :
    ∃ z, refAdd x y = ok z ∧ z.val ≤ 2147483647 := by
  have hP := P32_val
  obtain ⟨s, hs, vs⟩ := add_ok x y (by rw [max32]; omega)
  by_cases hge : 2147483647 ≤ s.val
  · obtain ⟨r, hr, vr⟩ := sub_ok s P32 (by rw [P32_val]; exact hge)
    have hc : s ≥ P32 := (ge_P32_iff _).mpr hge
    refine ⟨r, ?_, by rw [vr, P32_val]; omega⟩
    simp only [refAdd, bind_tc_ok, hs, hc, ↓reduceIte, hr]
  · have hn : ¬ (s ≥ P32) := fun h => hge ((ge_P32_iff _).mp h)
    refine ⟨s, ?_, by omega⟩
    simp only [refAdd, bind_tc_ok, hs, hn, ↓reduceIte]

theorem refSub_weak (x y : U32) (hx : x.val ≤ 2147483647) (hy : y.val ≤ 2147483647) :
    ∃ z, refSub x y = ok z ∧ z.val ≤ 2147483647 := by
  have hP := P32_val
  obtain ⟨i, hi, vi⟩ := add_ok x P32 (by rw [P32_val, max32]; omega)
  obtain ⟨s, hs, vs⟩ := sub_ok i y (by rw [vi, P32_val]; omega)
  by_cases hge : 2147483647 ≤ s.val
  · obtain ⟨r, hr, vr⟩ := sub_ok s P32 (by rw [P32_val]; exact hge)
    have hc : s ≥ P32 := (ge_P32_iff _).mpr hge
    refine ⟨r, ?_, by rw [vr, P32_val, vs, vi, P32_val]; omega⟩
    simp only [refSub, bind_tc_ok, hi, hs, hc, ↓reduceIte, hr]
  · have hn : ¬ (s ≥ P32) := fun h => hge ((ge_P32_iff _).mp h)
    refine ⟨s, ?_, by omega⟩
    simp only [refSub, bind_tc_ok, hi, hs, hn, ↓reduceIte]

theorem add_R22_weak (x y : U32) (hx : x.val ≤ 2147483647) (hy : y.val ≤ 2147483647) :
    ∃ z, refAdd x y = ok z ∧ z.val ≤ 2147483647 ∧ NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  obtain ⟨z, hz, hc⟩ := refAdd_weak x y hx hy
  obtain ⟨hs, hw⟩ := success_noOverflow_agrees _ _ ((checked_addCode x y).trans hz)
  exact ⟨z, hz, hc, hs, hw⟩

theorem sub_R22_weak (x y : U32) (hx : x.val ≤ 2147483647) (hy : y.val ≤ 2147483647) :
    ∃ z, refSub x y = ok z ∧ z.val ≤ 2147483647 ∧ NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  obtain ⟨z, hz, hc⟩ := refSub_weak x y hx hy
  obtain ⟨hs, hw⟩ := success_noOverflow_agrees _ _ ((checked_subCode x y).trans hz)
  exact ⟨z, hz, hc, hs, hw⟩

/-- The weak domain is maximal for subtraction's first checked step: at x = 2^31 + 2^31-1
the checked `x + P` overflows (so a limb above 2^31 must never reach M31::sub). -/
theorem sub_outside_weak_fails (z : U32) : refSub 2147483649#u32 0#u32 ≠ ok z := by
  intro h
  unfold refSub at h
  cases hc : (2147483649#u32 + P32 : Result U32) with
  | ok s => have hb := (add_success _ _ _ hc).2; exact absurd hb (by decide)
  | fail e => rw [hc] at h; cases h
  | div => rw [hc] at h; cases h

theorem CW_CM31_mul_weak (a b : AspisR1CurrentWide.field.CM31)
    (ha : a.a.val ≤ 2147483647) (hb : a.b.val ≤ 2147483647)
    (hc : b.a.val ≤ 2147483647) (hd : b.b.val ≤ 2147483647) :
    ∃ z, AspisR1CurrentWide.field.CM31.mul a b = ok z ∧ z.a.val ≤ 2147483647 ∧ z.b.val ≤ 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_okw i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm⟩ := refSub_weak m0 m1 (by omega) (by omega)
  obtain ⟨m3, hm3, vm3⟩ := refSub_weak m2 m0 (by omega) (by omega)
  obtain ⟨m4, hm4, vm4⟩ := refSub_weak m3 m1 vm3 (by omega)
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1CurrentWide.field.CM31.mul, CW_M31_mul_eq, CW_M31_sub_eq, CW_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem QA_CM31_mul_weak (a b : AspisR1Qm31ArithmeticProbe.field.CM31)
    (ha : a.a.val ≤ 2147483647) (hb : a.b.val ≤ 2147483647)
    (hc : b.a.val ≤ 2147483647) (hd : b.b.val ≤ 2147483647) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.CM31.mul a b = ok z ∧ z.a.val ≤ 2147483647 ∧ z.b.val ≤ 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_okw i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm⟩ := refSub_weak m0 m1 (by omega) (by omega)
  obtain ⟨m3, hm3, vm3⟩ := refSub_weak m2 m0 (by omega) (by omega)
  obtain ⟨m4, hm4, vm4⟩ := refSub_weak m3 m1 vm3 (by omega)
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.mul, QA_M31_mul_eq, QA_M31_sub_eq, QA_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem SM_CM31_mul_weak (a b : AspisR1SelectedMaskProbe.field.CM31)
    (ha : a.a.val ≤ 2147483647) (hb : a.b.val ≤ 2147483647)
    (hc : b.a.val ≤ 2147483647) (hd : b.b.val ≤ 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.mul a b = ok z ∧ z.a.val ≤ 2147483647 ∧ z.b.val ≤ 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_okw i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm⟩ := refSub_weak m0 m1 (by omega) (by omega)
  obtain ⟨m3, hm3, vm3⟩ := refSub_weak m2 m0 (by omega) (by omega)
  obtain ⟨m4, hm4, vm4⟩ := refSub_weak m3 m1 vm3 (by omega)
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1SelectedMaskProbe.field.CM31.mul, SM_M31_mul_eq, SM_M31_sub_eq, SM_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem SC_CM31_mul_weak (a b : AspisR1SemanticCallExtraction.aspis_core.field.CM31)
    (ha : a.a.val ≤ 2147483647) (hb : a.b.val ≤ 2147483647)
    (hc : b.a.val ≤ 2147483647) (hd : b.b.val ≤ 2147483647) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul a b = ok z ∧ z.a.val ≤ 2147483647 ∧ z.b.val ≤ 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_okw i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm⟩ := refSub_weak m0 m1 (by omega) (by omega)
  obtain ⟨m3, hm3, vm3⟩ := refSub_weak m2 m0 (by omega) (by omega)
  obtain ⟨m4, hm4, vm4⟩ := refSub_weak m3 m1 vm3 (by omega)
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul, SC_M31_mul_eq, SC_M31_sub_eq, SC_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem FIq_CM31_mul_weak (a b : FIq_Native.field.CM31)
    (ha : a.a.val ≤ 2147483647) (hb : a.b.val ≤ 2147483647)
    (hc : b.a.val ≤ 2147483647) (hd : b.b.val ≤ 2147483647) :
    ∃ z, FIq_Native.field.CM31.mul a b = ok z ∧ z.a.val ≤ 2147483647 ∧ z.b.val ≤ 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_okw i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm⟩ := refSub_weak m0 m1 (by omega) (by omega)
  obtain ⟨m3, hm3, vm3⟩ := refSub_weak m2 m0 (by omega) (by omega)
  obtain ⟨m4, hm4, vm4⟩ := refSub_weak m3 m1 vm3 (by omega)
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [FIq_Native.field.CM31.mul, FIq_M31_mul_eq, FIq_M31_sub_eq, FIq_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem R72_CM31_mul_weak (a b : AspisR72Sampler.field.CM31)
    (ha : a.a.val ≤ 2147483647) (hb : a.b.val ≤ 2147483647)
    (hc : b.a.val ≤ 2147483647) (hd : b.b.val ≤ 2147483647) :
    ∃ z, AspisR72Sampler.field.CM31.mul a b = ok z ∧ z.a.val ≤ 2147483647 ∧ z.b.val ≤ 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := R72_M31_mul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := R72_M31_mul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := r23_totalw i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm⟩ := refSub_weak m0 m1 (by omega) (by omega)
  obtain ⟨m3, hm3, vm3⟩ := refSub_weak m2 m0 (by omega) (by omega)
  obtain ⟨m4, hm4, vm4⟩ := refSub_weak m3 m1 vm3 (by omega)
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR72Sampler.field.CM31.mul, R72_M31_sub_eq, R72_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

#print axioms cross_okw
#print axioms r23_totalw
#print axioms refAdd_weak
#print axioms refSub_weak
#print axioms add_R22_weak
#print axioms sub_R22_weak
#print axioms sub_outside_weak_fails
#print axioms CW_CM31_mul_weak
#print axioms QA_CM31_mul_weak
#print axioms SM_CM31_mul_weak
#print axioms SC_CM31_mul_weak
#print axioms FIq_CM31_mul_weak
#print axioms R72_CM31_mul_weak
end AspisR1.NPH_R22Weak