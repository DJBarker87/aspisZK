import NPH_R22Producers
import RPu_FIq_Native02

/-! NPH_ (R22, separate limb invariant, step 2): tower lemmas for the SelectedMaskProbe (SM),
SemanticCallExtraction (SC), FIq_Native (FIq) and AspisR72Sampler (R72) copies, in the pattern
of NPH_R22Producers (CW/QA). W is limbs ≤ P. Each reached tower definition of these copies
maps W inputs to an ok W output (mul_m31 for any M31 operand; CM31.square with the weak
Karatsuba bound (2P)^2 < 2^64, through r23_product_u32_bounded for R72). Not covered: the R72
QM31.mul (its first step r24_canonical_mul is OPEN: NO_FROZEN_COUNTERPART) and the FIq
prepared-multiplier family. Standard axioms; no merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Towers
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22CM31 AspisR1.NPH_R22Weak

/-! ### AspisR1SelectedMaskProbe.field (SM) -/
abbrev SM_WC (c : AspisR1SelectedMaskProbe.field.CM31) : Prop := c.a.val ≤ 2147483647 ∧ c.b.val ≤ 2147483647
abbrev SM_WQ (q : AspisR1SelectedMaskProbe.field.QM31) : Prop := SM_WC q.c0 ∧ SM_WC q.c1

theorem SM_M31_mul_lt (x y : U32) : ∃ z, AspisR1SelectedMaskProbe.field.M31.mul x y = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨z, hz, hv⟩ := refMul_total x y
  exact ⟨z, by rw [SM_M31_mul_eq]; exact hz, by omega⟩

theorem SM_M31_double_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.double x = ok z ∧ z.val ≤ 2147483647 := by
  unfold AspisR1SelectedMaskProbe.field.M31.double; rw [SM_M31_add_eq]; exact refAdd_weak x x hx hx

theorem SM_M31_neg_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.neg x = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨z, hz, hv, _⟩ := refNeg_total x hx
  exact ⟨z, by rw [SM_M31_neg_eq]; exact hz, by omega⟩

theorem SM_CM31_add_weak (a b : AspisR1SelectedMaskProbe.field.CM31) (ha : SM_WC a) (hb : SM_WC b) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.add a b = ok z ∧ SM_WC z := by
  obtain ⟨m, hm, vm⟩ := refAdd_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refAdd_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1SelectedMaskProbe.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1SelectedMaskProbe.field.CM31.add, SM_M31_add_eq, hm, hm1, bind_tc_ok]

theorem SM_CM31_sub_weak (a b : AspisR1SelectedMaskProbe.field.CM31) (ha : SM_WC a) (hb : SM_WC b) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.sub a b = ok z ∧ SM_WC z := by
  obtain ⟨m, hm, vm⟩ := refSub_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1SelectedMaskProbe.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1SelectedMaskProbe.field.CM31.sub, SM_M31_sub_eq, hm, hm1, bind_tc_ok]

theorem SM_CM31_double_weak (a : AspisR1SelectedMaskProbe.field.CM31) (ha : SM_WC a) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.double a = ok z ∧ SM_WC z := by
  unfold AspisR1SelectedMaskProbe.field.CM31.double; exact SM_CM31_add_weak a a ha ha

theorem SM_CM31_new_weak (a b : U32) (ha : a.val ≤ 2147483647) (hb : b.val ≤ 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.new a b = ok z ∧ SM_WC z := ⟨_, rfl, ha, hb⟩

theorem SM_CM31_mul_m31_weak (a : AspisR1SelectedMaskProbe.field.CM31) (r : U32) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.mul_m31 a r = ok z ∧ SM_WC z := by
  obtain ⟨m, hm, vm⟩ := SM_M31_mul_lt a.a r
  obtain ⟨m1, hm1, vm1⟩ := SM_M31_mul_lt a.b r
  exact ⟨({ a := m, b := m1 } : AspisR1SelectedMaskProbe.field.CM31), by simp only [AspisR1SelectedMaskProbe.field.CM31.mul_m31, hm, hm1, bind_tc_ok], vm, vm1⟩

theorem SM_CM31_square_weak (a : AspisR1SelectedMaskProbe.field.CM31) (ha : SM_WC a) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.square a = ok z ∧ SM_WC z := by
  have hPv : (AspisR1SelectedMaskProbe.field.P).val = 2147483647 := by unfold AspisR1SelectedMaskProbe.field.P; rfl
  have h1 := ha.1
  have h2 := ha.2
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i7, h7, v7⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from AspisR1SelectedMaskProbe.field.P)
    (by rw [from_val, from_val, hPv, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := sub_ok i7 (core.convert.num.FromU64U32.from a.b)
    (by rw [v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨i10, h10, _⟩ := cross_okw i4 i9 (by rw [v4, from_val, from_val]; omega)
    (by rw [v9, v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨m, hm, vm⟩ := refReduce_total i10
  obtain ⟨m1, hm1, vm1⟩ := SM_M31_mul_lt a.a a.b
  obtain ⟨m2, hm2, vm2⟩ := SM_M31_double_weak m1 vm1
  refine ⟨{ a := m, b := m2 }, ?_, Nat.le_of_lt vm, vm2⟩
  simp only [AspisR1SelectedMaskProbe.field.CM31.square, SM_reduce_wrapper, lift, bind_tc_ok, h4, h7, h9, h10, hm, hm1, hm2]

theorem SM_mul_by_r_weak (x : AspisR1SelectedMaskProbe.field.CM31) (hx : SM_WC x) :
    ∃ z, AspisR1SelectedMaskProbe.field.mul_by_r x = ok z ∧ SM_WC z := by
  obtain ⟨m, hm, vm⟩ := SM_M31_double_weak x.a hx.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak m x.b vm hx.2
  obtain ⟨m2, hm2, vm2⟩ := SM_M31_double_weak x.b hx.2
  obtain ⟨m3, hm3, vm3⟩ := refAdd_weak x.a m2 hx.1 vm2
  refine ⟨({ a := m1, b := m3 } : AspisR1SelectedMaskProbe.field.CM31), ?_, vm1, vm3⟩
  simp only [AspisR1SelectedMaskProbe.field.mul_by_r, SM_M31_sub_eq, SM_M31_add_eq, hm, hm1, hm2, hm3, bind_tc_ok]

theorem SM_QM31_add_weak (a b : AspisR1SelectedMaskProbe.field.QM31) (ha : SM_WQ a) (hb : SM_WQ b) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.add a b = ok z ∧ SM_WQ z := by
  obtain ⟨c, hc, vc⟩ := SM_CM31_add_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := SM_CM31_add_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : AspisR1SelectedMaskProbe.field.QM31), ?_, vc, vc1⟩
  simp only [AspisR1SelectedMaskProbe.field.QM31.add, hc, hc1, bind_tc_ok]

theorem SM_QM31_mul_weak (a b : AspisR1SelectedMaskProbe.field.QM31) (ha : SM_WQ a) (hb : SM_WQ b) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.mul a b = ok z ∧ SM_WQ z := by
  obtain ⟨m0, h0, v0a, v0b⟩ := SM_CM31_mul_weak a.c0 b.c0 ha.1.1 ha.1.2 hb.1.1 hb.1.2
  obtain ⟨m1, h1, v1a, v1b⟩ := SM_CM31_mul_weak a.c1 b.c1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  obtain ⟨c, hc, vc⟩ := SM_CM31_add_weak a.c0 a.c1 ha.1 ha.2
  obtain ⟨c1, hc1, vc1⟩ := SM_CM31_add_weak b.c0 b.c1 hb.1 hb.2
  obtain ⟨m2, h2, v2a, v2b⟩ := SM_CM31_mul_weak c c1 vc.1 vc.2 vc1.1 vc1.2
  obtain ⟨c2, hc2, vc2⟩ := SM_mul_by_r_weak m1 ⟨v1a, v1b⟩
  obtain ⟨c3, hc3, vc3⟩ := SM_CM31_add_weak m0 c2 ⟨v0a, v0b⟩ vc2
  obtain ⟨c4, hc4, vc4⟩ := SM_CM31_sub_weak m2 m0 ⟨v2a, v2b⟩ ⟨v0a, v0b⟩
  obtain ⟨c5, hc5, vc5⟩ := SM_CM31_sub_weak c4 m1 vc4 ⟨v1a, v1b⟩
  refine ⟨({ c0 := c3, c1 := c5 } : AspisR1SelectedMaskProbe.field.QM31), ?_, vc3, vc5⟩
  simp only [AspisR1SelectedMaskProbe.field.QM31.mul, h0, h1, hc, hc1, h2, hc2, hc3, hc4, hc5, bind_tc_ok]

theorem SM_QM31_mul_m31_weak (q : AspisR1SelectedMaskProbe.field.QM31) (r : U32) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.mul_m31 q r = ok z ∧ SM_WQ z := by
  obtain ⟨c, hc, vc⟩ := SM_CM31_mul_m31_weak q.c0 r
  obtain ⟨c1, hc1, vc1⟩ := SM_CM31_mul_m31_weak q.c1 r
  exact ⟨({ c0 := c, c1 := c1 } : AspisR1SelectedMaskProbe.field.QM31), by simp only [AspisR1SelectedMaskProbe.field.QM31.mul_m31, hc, hc1, bind_tc_ok], vc, vc1⟩

theorem SM_QM31_square_weak (q : AspisR1SelectedMaskProbe.field.QM31) (hq : SM_WQ q) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.square q = ok z ∧ SM_WQ z := by
  obtain ⟨s0, hs0, vs0⟩ := SM_CM31_square_weak q.c0 hq.1
  obtain ⟨s1, hs1, vs1⟩ := SM_CM31_square_weak q.c1 hq.2
  obtain ⟨c, hc, vc⟩ := SM_mul_by_r_weak s1 vs1
  obtain ⟨c1, hc1, vc1⟩ := SM_CM31_add_weak s0 c vs0 vc
  obtain ⟨c2, hc2, v2a, v2b⟩ := SM_CM31_mul_weak q.c0 q.c1 hq.1.1 hq.1.2 hq.2.1 hq.2.2
  obtain ⟨c3, hc3, vc3⟩ := SM_CM31_double_weak c2 ⟨v2a, v2b⟩
  refine ⟨({ c0 := c1, c1 := c3 } : AspisR1SelectedMaskProbe.field.QM31), ?_, vc1, vc3⟩
  simp only [AspisR1SelectedMaskProbe.field.QM31.square, hs0, hs1, hc, hc1, hc2, hc3, bind_tc_ok]

/-! ### AspisR1SemanticCallExtraction.aspis_core.field (SC) -/
abbrev SC_WC (c : AspisR1SemanticCallExtraction.aspis_core.field.CM31) : Prop := c.a.val ≤ 2147483647 ∧ c.b.val ≤ 2147483647
abbrev SC_WQ (q : AspisR1SemanticCallExtraction.aspis_core.field.QM31) : Prop := SC_WC q.c0 ∧ SC_WC q.c1

theorem SC_M31_mul_lt (x y : U32) : ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨z, hz, hv⟩ := refMul_total x y
  exact ⟨z, by rw [SC_M31_mul_eq]; exact hz, by omega⟩

theorem SC_M31_double_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.double x = ok z ∧ z.val ≤ 2147483647 := by
  unfold AspisR1SemanticCallExtraction.aspis_core.field.M31.double; rw [SC_M31_add_eq]; exact refAdd_weak x x hx hx

theorem SC_CM31_add_weak (a b : AspisR1SemanticCallExtraction.aspis_core.field.CM31) (ha : SC_WC a) (hb : SC_WC b) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.CM31.add a b = ok z ∧ SC_WC z := by
  obtain ⟨m, hm, vm⟩ := refAdd_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refAdd_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1SemanticCallExtraction.aspis_core.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.CM31.add, SC_M31_add_eq, hm, hm1, bind_tc_ok]

theorem SC_CM31_sub_weak (a b : AspisR1SemanticCallExtraction.aspis_core.field.CM31) (ha : SC_WC a) (hb : SC_WC b) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.CM31.sub a b = ok z ∧ SC_WC z := by
  obtain ⟨m, hm, vm⟩ := refSub_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1SemanticCallExtraction.aspis_core.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.CM31.sub, SC_M31_sub_eq, hm, hm1, bind_tc_ok]

theorem SC_mul_by_r_weak (x : AspisR1SemanticCallExtraction.aspis_core.field.CM31) (hx : SC_WC x) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r x = ok z ∧ SC_WC z := by
  obtain ⟨m, hm, vm⟩ := SC_M31_double_weak x.a hx.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak m x.b vm hx.2
  obtain ⟨m2, hm2, vm2⟩ := SC_M31_double_weak x.b hx.2
  obtain ⟨m3, hm3, vm3⟩ := refAdd_weak x.a m2 hx.1 vm2
  refine ⟨({ a := m1, b := m3 } : AspisR1SemanticCallExtraction.aspis_core.field.CM31), ?_, vm1, vm3⟩
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r, SC_M31_sub_eq, SC_M31_add_eq, hm, hm1, hm2, hm3, bind_tc_ok]

theorem SC_QM31_add_weak (a b : AspisR1SemanticCallExtraction.aspis_core.field.QM31) (ha : SC_WQ a) (hb : SC_WQ b) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.QM31.add a b = ok z ∧ SC_WQ z := by
  obtain ⟨c, hc, vc⟩ := SC_CM31_add_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := SC_CM31_add_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : AspisR1SemanticCallExtraction.aspis_core.field.QM31), ?_, vc, vc1⟩
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.QM31.add, hc, hc1, bind_tc_ok]

theorem SC_QM31_mul_weak (a b : AspisR1SemanticCallExtraction.aspis_core.field.QM31) (ha : SC_WQ a) (hb : SC_WQ b) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul a b = ok z ∧ SC_WQ z := by
  obtain ⟨m0, h0, v0a, v0b⟩ := SC_CM31_mul_weak a.c0 b.c0 ha.1.1 ha.1.2 hb.1.1 hb.1.2
  obtain ⟨m1, h1, v1a, v1b⟩ := SC_CM31_mul_weak a.c1 b.c1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  obtain ⟨c, hc, vc⟩ := SC_CM31_add_weak a.c0 a.c1 ha.1 ha.2
  obtain ⟨c1, hc1, vc1⟩ := SC_CM31_add_weak b.c0 b.c1 hb.1 hb.2
  obtain ⟨m2, h2, v2a, v2b⟩ := SC_CM31_mul_weak c c1 vc.1 vc.2 vc1.1 vc1.2
  obtain ⟨c2, hc2, vc2⟩ := SC_mul_by_r_weak m1 ⟨v1a, v1b⟩
  obtain ⟨c3, hc3, vc3⟩ := SC_CM31_add_weak m0 c2 ⟨v0a, v0b⟩ vc2
  obtain ⟨c4, hc4, vc4⟩ := SC_CM31_sub_weak m2 m0 ⟨v2a, v2b⟩ ⟨v0a, v0b⟩
  obtain ⟨c5, hc5, vc5⟩ := SC_CM31_sub_weak c4 m1 vc4 ⟨v1a, v1b⟩
  refine ⟨({ c0 := c3, c1 := c5 } : AspisR1SemanticCallExtraction.aspis_core.field.QM31), ?_, vc3, vc5⟩
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul, h0, h1, hc, hc1, h2, hc2, hc3, hc4, hc5, bind_tc_ok]

/-! ### FIq_Native.field (FIq) -/
abbrev FIq_WC (c : FIq_Native.field.CM31) : Prop := c.a.val ≤ 2147483647 ∧ c.b.val ≤ 2147483647
abbrev FIq_WQ (q : FIq_Native.field.QM31) : Prop := FIq_WC q.c0 ∧ FIq_WC q.c1

theorem FIq_M31_mul_lt (x y : U32) : ∃ z, FIq_Native.field.M31.mul x y = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨z, hz, hv⟩ := refMul_total x y
  exact ⟨z, by rw [FIq_M31_mul_eq]; exact hz, by omega⟩

theorem FIq_M31_double_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, FIq_Native.field.M31.double x = ok z ∧ z.val ≤ 2147483647 := by
  unfold FIq_Native.field.M31.double; rw [FIq_M31_add_eq]; exact refAdd_weak x x hx hx

theorem FIq_CM31_add_weak (a b : FIq_Native.field.CM31) (ha : FIq_WC a) (hb : FIq_WC b) :
    ∃ z, FIq_Native.field.CM31.add a b = ok z ∧ FIq_WC z := by
  obtain ⟨m, hm, vm⟩ := refAdd_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refAdd_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : FIq_Native.field.CM31), ?_, vm, vm1⟩
  simp only [FIq_Native.field.CM31.add, FIq_M31_add_eq, hm, hm1, bind_tc_ok]

theorem FIq_CM31_sub_weak (a b : FIq_Native.field.CM31) (ha : FIq_WC a) (hb : FIq_WC b) :
    ∃ z, FIq_Native.field.CM31.sub a b = ok z ∧ FIq_WC z := by
  obtain ⟨m, hm, vm⟩ := refSub_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : FIq_Native.field.CM31), ?_, vm, vm1⟩
  simp only [FIq_Native.field.CM31.sub, FIq_M31_sub_eq, hm, hm1, bind_tc_ok]

theorem FIq_CM31_double_weak (a : FIq_Native.field.CM31) (ha : FIq_WC a) :
    ∃ z, FIq_Native.field.CM31.double a = ok z ∧ FIq_WC z := by
  unfold FIq_Native.field.CM31.double; exact FIq_CM31_add_weak a a ha ha

theorem FIq_CM31_new_weak (a b : U32) (ha : a.val ≤ 2147483647) (hb : b.val ≤ 2147483647) :
    ∃ z, FIq_Native.field.CM31.new a b = ok z ∧ FIq_WC z := ⟨_, rfl, ha, hb⟩

theorem FIq_CM31_mul_m31_weak (a : FIq_Native.field.CM31) (r : U32) :
    ∃ z, FIq_Native.field.CM31.mul_m31 a r = ok z ∧ FIq_WC z := by
  obtain ⟨m, hm, vm⟩ := FIq_M31_mul_lt a.a r
  obtain ⟨m1, hm1, vm1⟩ := FIq_M31_mul_lt a.b r
  exact ⟨({ a := m, b := m1 } : FIq_Native.field.CM31), by simp only [FIq_Native.field.CM31.mul_m31, hm, hm1, bind_tc_ok], vm, vm1⟩

theorem FIq_CM31_square_weak (a : FIq_Native.field.CM31) (ha : FIq_WC a) :
    ∃ z, FIq_Native.field.CM31.square a = ok z ∧ FIq_WC z := by
  have hPv : (FIq_Native.field.P).val = 2147483647 := by unfold FIq_Native.field.P; rfl
  have h1 := ha.1
  have h2 := ha.2
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i7, h7, v7⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from FIq_Native.field.P)
    (by rw [from_val, from_val, hPv, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := sub_ok i7 (core.convert.num.FromU64U32.from a.b)
    (by rw [v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨i10, h10, _⟩ := cross_okw i4 i9 (by rw [v4, from_val, from_val]; omega)
    (by rw [v9, v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨m, hm, vm⟩ := refReduce_total i10
  obtain ⟨m1, hm1, vm1⟩ := FIq_M31_mul_lt a.a a.b
  obtain ⟨m2, hm2, vm2⟩ := FIq_M31_double_weak m1 vm1
  refine ⟨{ a := m, b := m2 }, ?_, Nat.le_of_lt vm, vm2⟩
  simp only [FIq_Native.field.CM31.square, FIq_reduce_wrapper, lift, bind_tc_ok, h4, h7, h9, h10, hm, hm1, hm2]

theorem FIq_mul_by_r_weak (x : FIq_Native.field.CM31) (hx : FIq_WC x) :
    ∃ z, FIq_Native.field.mul_by_r x = ok z ∧ FIq_WC z := by
  obtain ⟨m, hm, vm⟩ := FIq_M31_double_weak x.a hx.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak m x.b vm hx.2
  obtain ⟨m2, hm2, vm2⟩ := FIq_M31_double_weak x.b hx.2
  obtain ⟨m3, hm3, vm3⟩ := refAdd_weak x.a m2 hx.1 vm2
  refine ⟨({ a := m1, b := m3 } : FIq_Native.field.CM31), ?_, vm1, vm3⟩
  simp only [FIq_Native.field.mul_by_r, FIq_M31_sub_eq, FIq_M31_add_eq, hm, hm1, hm2, hm3, bind_tc_ok]

theorem FIq_QM31_add_weak (a b : FIq_Native.field.QM31) (ha : FIq_WQ a) (hb : FIq_WQ b) :
    ∃ z, FIq_Native.field.QM31.add a b = ok z ∧ FIq_WQ z := by
  obtain ⟨c, hc, vc⟩ := FIq_CM31_add_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := FIq_CM31_add_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : FIq_Native.field.QM31), ?_, vc, vc1⟩
  simp only [FIq_Native.field.QM31.add, hc, hc1, bind_tc_ok]

theorem FIq_QM31_sub_weak (a b : FIq_Native.field.QM31) (ha : FIq_WQ a) (hb : FIq_WQ b) :
    ∃ z, FIq_Native.field.QM31.sub a b = ok z ∧ FIq_WQ z := by
  obtain ⟨c, hc, vc⟩ := FIq_CM31_sub_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := FIq_CM31_sub_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : FIq_Native.field.QM31), ?_, vc, vc1⟩
  simp only [FIq_Native.field.QM31.sub, hc, hc1, bind_tc_ok]

theorem FIq_QM31_mul_weak (a b : FIq_Native.field.QM31) (ha : FIq_WQ a) (hb : FIq_WQ b) :
    ∃ z, FIq_Native.field.QM31.mul a b = ok z ∧ FIq_WQ z := by
  obtain ⟨m0, h0, v0a, v0b⟩ := FIq_CM31_mul_weak a.c0 b.c0 ha.1.1 ha.1.2 hb.1.1 hb.1.2
  obtain ⟨m1, h1, v1a, v1b⟩ := FIq_CM31_mul_weak a.c1 b.c1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  obtain ⟨c, hc, vc⟩ := FIq_CM31_add_weak a.c0 a.c1 ha.1 ha.2
  obtain ⟨c1, hc1, vc1⟩ := FIq_CM31_add_weak b.c0 b.c1 hb.1 hb.2
  obtain ⟨m2, h2, v2a, v2b⟩ := FIq_CM31_mul_weak c c1 vc.1 vc.2 vc1.1 vc1.2
  obtain ⟨c2, hc2, vc2⟩ := FIq_mul_by_r_weak m1 ⟨v1a, v1b⟩
  obtain ⟨c3, hc3, vc3⟩ := FIq_CM31_add_weak m0 c2 ⟨v0a, v0b⟩ vc2
  obtain ⟨c4, hc4, vc4⟩ := FIq_CM31_sub_weak m2 m0 ⟨v2a, v2b⟩ ⟨v0a, v0b⟩
  obtain ⟨c5, hc5, vc5⟩ := FIq_CM31_sub_weak c4 m1 vc4 ⟨v1a, v1b⟩
  refine ⟨({ c0 := c3, c1 := c5 } : FIq_Native.field.QM31), ?_, vc3, vc5⟩
  simp only [FIq_Native.field.QM31.mul, h0, h1, hc, hc1, h2, hc2, hc3, hc4, hc5, bind_tc_ok]

theorem FIq_QM31_mul_m31_weak (q : FIq_Native.field.QM31) (r : U32) :
    ∃ z, FIq_Native.field.QM31.mul_m31 q r = ok z ∧ FIq_WQ z := by
  obtain ⟨c, hc, vc⟩ := FIq_CM31_mul_m31_weak q.c0 r
  obtain ⟨c1, hc1, vc1⟩ := FIq_CM31_mul_m31_weak q.c1 r
  exact ⟨({ c0 := c, c1 := c1 } : FIq_Native.field.QM31), by simp only [FIq_Native.field.QM31.mul_m31, hc, hc1, bind_tc_ok], vc, vc1⟩

theorem FIq_QM31_square_weak (q : FIq_Native.field.QM31) (hq : FIq_WQ q) :
    ∃ z, FIq_Native.field.QM31.square q = ok z ∧ FIq_WQ z := by
  obtain ⟨s0, hs0, vs0⟩ := FIq_CM31_square_weak q.c0 hq.1
  obtain ⟨s1, hs1, vs1⟩ := FIq_CM31_square_weak q.c1 hq.2
  obtain ⟨c, hc, vc⟩ := FIq_mul_by_r_weak s1 vs1
  obtain ⟨c1, hc1, vc1⟩ := FIq_CM31_add_weak s0 c vs0 vc
  obtain ⟨c2, hc2, v2a, v2b⟩ := FIq_CM31_mul_weak q.c0 q.c1 hq.1.1 hq.1.2 hq.2.1 hq.2.2
  obtain ⟨c3, hc3, vc3⟩ := FIq_CM31_double_weak c2 ⟨v2a, v2b⟩
  refine ⟨({ c0 := c1, c1 := c3 } : FIq_Native.field.QM31), ?_, vc1, vc3⟩
  simp only [FIq_Native.field.QM31.square, hs0, hs1, hc, hc1, hc2, hc3, bind_tc_ok]

/-! ### AspisR72Sampler.field (R72) -/
abbrev R72_WC (c : AspisR72Sampler.field.CM31) : Prop := c.a.val ≤ 2147483647 ∧ c.b.val ≤ 2147483647
abbrev R72_WQ (q : AspisR72Sampler.field.QM31) : Prop := R72_WC q.c0 ∧ R72_WC q.c1

theorem R72_M31_mul_lt (x y : U32) : ∃ z, AspisR72Sampler.field.M31.mul x y = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨z, hz, hv⟩ := R72_M31_mul_total x y
  exact ⟨z, hz, by omega⟩

theorem R72_M31_double_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, AspisR72Sampler.field.M31.double x = ok z ∧ z.val ≤ 2147483647 := by
  unfold AspisR72Sampler.field.M31.double; rw [R72_M31_add_eq]; exact refAdd_weak x x hx hx

theorem R72_M31_neg_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, AspisR72Sampler.field.M31.neg x = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨z, hz, hv, _⟩ := refNeg_total x hx
  exact ⟨z, by rw [R72_M31_neg_eq]; exact hz, by omega⟩

theorem R72_CM31_add_weak (a b : AspisR72Sampler.field.CM31) (ha : R72_WC a) (hb : R72_WC b) :
    ∃ z, AspisR72Sampler.field.CM31.add a b = ok z ∧ R72_WC z := by
  obtain ⟨m, hm, vm⟩ := refAdd_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refAdd_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR72Sampler.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR72Sampler.field.CM31.add, R72_M31_add_eq, hm, hm1, bind_tc_ok]

theorem R72_CM31_sub_weak (a b : AspisR72Sampler.field.CM31) (ha : R72_WC a) (hb : R72_WC b) :
    ∃ z, AspisR72Sampler.field.CM31.sub a b = ok z ∧ R72_WC z := by
  obtain ⟨m, hm, vm⟩ := refSub_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR72Sampler.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR72Sampler.field.CM31.sub, R72_M31_sub_eq, hm, hm1, bind_tc_ok]

theorem R72_CM31_neg_weak (a : AspisR72Sampler.field.CM31) (ha : R72_WC a) :
    ∃ z, AspisR72Sampler.field.CM31.neg a = ok z ∧ R72_WC z := by
  obtain ⟨m, hm, vm⟩ := R72_M31_neg_weak a.a ha.1
  obtain ⟨m1, hm1, vm1⟩ := R72_M31_neg_weak a.b ha.2
  exact ⟨({ a := m, b := m1 } : AspisR72Sampler.field.CM31), by simp only [AspisR72Sampler.field.CM31.neg, hm, hm1, bind_tc_ok], vm, vm1⟩

theorem R72_CM31_double_weak (a : AspisR72Sampler.field.CM31) (ha : R72_WC a) :
    ∃ z, AspisR72Sampler.field.CM31.double a = ok z ∧ R72_WC z := by
  unfold AspisR72Sampler.field.CM31.double; exact R72_CM31_add_weak a a ha ha

theorem R72_CM31_new_weak (a b : U32) (ha : a.val ≤ 2147483647) (hb : b.val ≤ 2147483647) :
    ∃ z, AspisR72Sampler.field.CM31.new a b = ok z ∧ R72_WC z := ⟨_, rfl, ha, hb⟩

theorem R72_CM31_square_weak (a : AspisR72Sampler.field.CM31) (ha : R72_WC a) :
    ∃ z, AspisR72Sampler.field.CM31.square a = ok z ∧ R72_WC z := by
  have hPv : (AspisR72Sampler.field.P).val = 2147483647 := by unfold AspisR72Sampler.field.P; rfl
  have h1 := ha.1
  have h2 := ha.2
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i7, h7, v7⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from AspisR72Sampler.field.P)
    (by rw [from_val, from_val, hPv, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := sub_ok i7 (core.convert.num.FromU64U32.from a.b)
    (by rw [v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨i10, h10, _⟩ := r23_totalw i4 i9 (by rw [v4, from_val, from_val]; omega)
    (by rw [v9, v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨m, hm, vm⟩ := refReduce_total i10
  obtain ⟨m1, hm1, vm1⟩ := R72_M31_mul_lt a.a a.b
  obtain ⟨m2, hm2, vm2⟩ := R72_M31_double_weak m1 vm1
  refine ⟨{ a := m, b := m2 }, ?_, Nat.le_of_lt vm, vm2⟩
  simp only [AspisR72Sampler.field.CM31.square, R72_reduce_wrapper, lift, bind_tc_ok, h4, h7, h9, h10, hm, hm1, hm2]

theorem R72_mul_by_r_weak (x : AspisR72Sampler.field.CM31) (hx : R72_WC x) :
    ∃ z, AspisR72Sampler.field.mul_by_r x = ok z ∧ R72_WC z := by
  obtain ⟨m, hm, vm⟩ := R72_M31_double_weak x.a hx.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak m x.b vm hx.2
  obtain ⟨m2, hm2, vm2⟩ := R72_M31_double_weak x.b hx.2
  obtain ⟨m3, hm3, vm3⟩ := refAdd_weak x.a m2 hx.1 vm2
  refine ⟨({ a := m1, b := m3 } : AspisR72Sampler.field.CM31), ?_, vm1, vm3⟩
  simp only [AspisR72Sampler.field.mul_by_r, R72_M31_sub_eq, R72_M31_add_eq, hm, hm1, hm2, hm3, bind_tc_ok]

theorem R72_QM31_add_weak (a b : AspisR72Sampler.field.QM31) (ha : R72_WQ a) (hb : R72_WQ b) :
    ∃ z, AspisR72Sampler.field.QM31.add a b = ok z ∧ R72_WQ z := by
  obtain ⟨c, hc, vc⟩ := R72_CM31_add_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := R72_CM31_add_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : AspisR72Sampler.field.QM31), ?_, vc, vc1⟩
  simp only [AspisR72Sampler.field.QM31.add, hc, hc1, bind_tc_ok]

theorem R72_QM31_sub_weak (a b : AspisR72Sampler.field.QM31) (ha : R72_WQ a) (hb : R72_WQ b) :
    ∃ z, AspisR72Sampler.field.QM31.sub a b = ok z ∧ R72_WQ z := by
  obtain ⟨c, hc, vc⟩ := R72_CM31_sub_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := R72_CM31_sub_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : AspisR72Sampler.field.QM31), ?_, vc, vc1⟩
  simp only [AspisR72Sampler.field.QM31.sub, hc, hc1, bind_tc_ok]

theorem R72_QM31_square_weak (q : AspisR72Sampler.field.QM31) (hq : R72_WQ q) :
    ∃ z, AspisR72Sampler.field.QM31.square q = ok z ∧ R72_WQ z := by
  obtain ⟨s0, hs0, vs0⟩ := R72_CM31_square_weak q.c0 hq.1
  obtain ⟨s1, hs1, vs1⟩ := R72_CM31_square_weak q.c1 hq.2
  obtain ⟨c, hc, vc⟩ := R72_mul_by_r_weak s1 vs1
  obtain ⟨c1, hc1, vc1⟩ := R72_CM31_add_weak s0 c vs0 vc
  obtain ⟨c2, hc2, v2a, v2b⟩ := R72_CM31_mul_weak q.c0 q.c1 hq.1.1 hq.1.2 hq.2.1 hq.2.2
  obtain ⟨c3, hc3, vc3⟩ := R72_CM31_double_weak c2 ⟨v2a, v2b⟩
  refine ⟨({ c0 := c1, c1 := c3 } : AspisR72Sampler.field.QM31), ?_, vc1, vc3⟩
  simp only [AspisR72Sampler.field.QM31.square, hs0, hs1, hc, hc1, hc2, hc3, bind_tc_ok]

#print axioms SM_M31_mul_lt
#print axioms SM_M31_double_weak
#print axioms SM_M31_neg_weak
#print axioms SM_CM31_add_weak
#print axioms SM_CM31_sub_weak
#print axioms SM_CM31_double_weak
#print axioms SM_CM31_new_weak
#print axioms SM_CM31_mul_m31_weak
#print axioms SM_CM31_square_weak
#print axioms SM_mul_by_r_weak
#print axioms SM_QM31_add_weak
#print axioms SM_QM31_mul_weak
#print axioms SM_QM31_mul_m31_weak
#print axioms SM_QM31_square_weak
#print axioms SC_M31_mul_lt
#print axioms SC_M31_double_weak
#print axioms SC_CM31_add_weak
#print axioms SC_CM31_sub_weak
#print axioms SC_mul_by_r_weak
#print axioms SC_QM31_add_weak
#print axioms SC_QM31_mul_weak
#print axioms FIq_M31_mul_lt
#print axioms FIq_M31_double_weak
#print axioms FIq_CM31_add_weak
#print axioms FIq_CM31_sub_weak
#print axioms FIq_CM31_double_weak
#print axioms FIq_CM31_new_weak
#print axioms FIq_CM31_mul_m31_weak
#print axioms FIq_CM31_square_weak
#print axioms FIq_mul_by_r_weak
#print axioms FIq_QM31_add_weak
#print axioms FIq_QM31_sub_weak
#print axioms FIq_QM31_mul_weak
#print axioms FIq_QM31_mul_m31_weak
#print axioms FIq_QM31_square_weak
#print axioms R72_M31_mul_lt
#print axioms R72_M31_double_weak
#print axioms R72_M31_neg_weak
#print axioms R72_CM31_add_weak
#print axioms R72_CM31_sub_weak
#print axioms R72_CM31_neg_weak
#print axioms R72_CM31_double_weak
#print axioms R72_CM31_new_weak
#print axioms R72_CM31_square_weak
#print axioms R72_mul_by_r_weak
#print axioms R72_QM31_add_weak
#print axioms R72_QM31_sub_weak
#print axioms R72_QM31_square_weak
end AspisR1.NPH_R22Towers
