import NPH_R22Weak
import ActualDecodeKStrictQM31Parser
import S8OwnedP6StrictParser

/-! NPH_ (R22, separate limb invariant, item (i)): producer lemmas.
- Strict decoders: every QM31 returned by the two strict 16-byte decoders in the cone
  (AspisR1DecodeKFullV10 and S8OwnedP6 `QM31.from_le_bytes`) has all four limbs < P, from the
  closure theorems `success_has_strict_limbs`.
- Kernel outputs: for the AspisR1CurrentWide (CW) and AspisR1Qm31ArithmeticProbe (QA) copies,
  M31.double, CM31.add/sub, mul_by_r and QM31.add/sub/mul map limbs ≤ P to ok limbs ≤ P
  (extending NPH_R22Weak from the 28 kernels to these field-module callers).
Standard axioms; no merged module or ops interface is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Producers
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22Weak

theorem value_lt (l : AspisR1.RetainedFieldByteCodec.M31Value) :
    (AspisR1.M31ParserRefinement.valueToU32 l).val < 2147483647 := by
  rw [AspisR1.M31ParserRefinement.valueToU32_val]
  have := l.isLt
  first | exact this | (norm_num [AspisR1.RetainedFieldByteCodec.m31Modulus, AspisR1.RetainedFieldByteCodec.rawCandidateCount] at this ⊢; omega) | omega

/-- Producer: the DecodeKFullV10 strict decoder returns limbs < P. -/
theorem decodeK_strict_limbs_lt (arr : Array U8 16#usize) (q : AspisR1DecodeKFullV10.aspis_core.field.QM31)
    (h : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr) = .ok (some q)) :
    q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧ q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647 := by
  obtain ⟨limbs, _, hq, _⟩ := AspisR1.ActualDecodeKStrictQM31Parser.success_has_strict_limbs arr q h
  subst hq
  exact ⟨value_lt _, value_lt _, value_lt _, value_lt _⟩

/-- Producer: the S8OwnedP6 strict decoder returns limbs < P. -/
theorem s8_strict_limbs_lt (arr : Array U8 16#usize) (q : S8OwnedP6.aspis_core.field.QM31)
    (h : S8OwnedP6.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr) = .ok (some q)) :
    q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧ q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647 := by
  obtain ⟨limbs, _, hq, _⟩ := AspisR1.S8OwnedP6StrictParser.success_has_strict_limbs arr q h
  subst hq
  exact ⟨value_lt _, value_lt _, value_lt _, value_lt _⟩

/-! ### AspisR1CurrentWide -/
abbrev CW_WC (c : AspisR1CurrentWide.field.CM31) : Prop := c.a.val ≤ 2147483647 ∧ c.b.val ≤ 2147483647
abbrev CW_WQ (q : AspisR1CurrentWide.field.QM31) : Prop := CW_WC q.c0 ∧ CW_WC q.c1

theorem CW_M31_double_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, AspisR1CurrentWide.field.M31.double x = ok z ∧ z.val ≤ 2147483647 := by
  unfold AspisR1CurrentWide.field.M31.double; rw [CW_M31_add_eq]; exact refAdd_weak x x hx hx

theorem CW_CM31_add_weak (a b : AspisR1CurrentWide.field.CM31) (ha : CW_WC a) (hb : CW_WC b) :
    ∃ z, AspisR1CurrentWide.field.CM31.add a b = ok z ∧ CW_WC z := by
  obtain ⟨m, hm, vm⟩ := refAdd_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refAdd_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1CurrentWide.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1CurrentWide.field.CM31.add, CW_M31_add_eq, hm, hm1, bind_tc_ok]

theorem CW_CM31_sub_weak (a b : AspisR1CurrentWide.field.CM31) (ha : CW_WC a) (hb : CW_WC b) :
    ∃ z, AspisR1CurrentWide.field.CM31.sub a b = ok z ∧ CW_WC z := by
  obtain ⟨m, hm, vm⟩ := refSub_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1CurrentWide.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1CurrentWide.field.CM31.sub, CW_M31_sub_eq, hm, hm1, bind_tc_ok]

theorem CW_mul_by_r_weak (x : AspisR1CurrentWide.field.CM31) (hx : CW_WC x) :
    ∃ z, AspisR1CurrentWide.field.mul_by_r x = ok z ∧ CW_WC z := by
  obtain ⟨m, hm, vm⟩ := CW_M31_double_weak x.a hx.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak m x.b vm hx.2
  obtain ⟨m2, hm2, vm2⟩ := CW_M31_double_weak x.b hx.2
  obtain ⟨m3, hm3, vm3⟩ := refAdd_weak x.a m2 hx.1 vm2
  refine ⟨({ a := m1, b := m3 } : AspisR1CurrentWide.field.CM31), ?_, vm1, vm3⟩
  simp only [AspisR1CurrentWide.field.mul_by_r, CW_M31_sub_eq, CW_M31_add_eq, hm, hm1, hm2, hm3, bind_tc_ok]

theorem CW_QM31_add_weak (a b : AspisR1CurrentWide.field.QM31) (ha : CW_WQ a) (hb : CW_WQ b) :
    ∃ z, AspisR1CurrentWide.field.QM31.add a b = ok z ∧ CW_WQ z := by
  obtain ⟨c, hc, vc⟩ := CW_CM31_add_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := CW_CM31_add_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : AspisR1CurrentWide.field.QM31), ?_, vc, vc1⟩
  simp only [AspisR1CurrentWide.field.QM31.add, hc, hc1, bind_tc_ok]

theorem CW_QM31_mul_weak (a b : AspisR1CurrentWide.field.QM31) (ha : CW_WQ a) (hb : CW_WQ b) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul a b = ok z ∧ CW_WQ z := by
  obtain ⟨m0, h0, v0a, v0b⟩ := CW_CM31_mul_weak a.c0 b.c0 ha.1.1 ha.1.2 hb.1.1 hb.1.2
  obtain ⟨m1, h1, v1a, v1b⟩ := CW_CM31_mul_weak a.c1 b.c1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  obtain ⟨c, hc, vc⟩ := CW_CM31_add_weak a.c0 a.c1 ha.1 ha.2
  obtain ⟨c1, hc1, vc1⟩ := CW_CM31_add_weak b.c0 b.c1 hb.1 hb.2
  obtain ⟨m2, h2, v2a, v2b⟩ := CW_CM31_mul_weak c c1 vc.1 vc.2 vc1.1 vc1.2
  obtain ⟨c2, hc2, vc2⟩ := CW_mul_by_r_weak m1 ⟨v1a, v1b⟩
  obtain ⟨c3, hc3, vc3⟩ := CW_CM31_add_weak m0 c2 ⟨v0a, v0b⟩ vc2
  obtain ⟨c4, hc4, vc4⟩ := CW_CM31_sub_weak m2 m0 ⟨v2a, v2b⟩ ⟨v0a, v0b⟩
  obtain ⟨c5, hc5, vc5⟩ := CW_CM31_sub_weak c4 m1 vc4 ⟨v1a, v1b⟩
  refine ⟨({ c0 := c3, c1 := c5 } : AspisR1CurrentWide.field.QM31), ?_, vc3, vc5⟩
  simp only [AspisR1CurrentWide.field.QM31.mul, h0, h1, hc, hc1, h2, hc2, hc3, hc4, hc5, bind_tc_ok]

theorem CW_QM31_sub_weak (a b : AspisR1CurrentWide.field.QM31) (ha : CW_WQ a) (hb : CW_WQ b) :
    ∃ z, AspisR1CurrentWide.field.QM31.sub a b = ok z ∧ CW_WQ z := by
  obtain ⟨c, hc, vc⟩ := CW_CM31_sub_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := CW_CM31_sub_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : AspisR1CurrentWide.field.QM31), ?_, vc, vc1⟩
  simp only [AspisR1CurrentWide.field.QM31.sub, hc, hc1, bind_tc_ok]

/-! ### AspisR1Qm31ArithmeticProbe -/
abbrev QA_WC (c : AspisR1Qm31ArithmeticProbe.field.CM31) : Prop := c.a.val ≤ 2147483647 ∧ c.b.val ≤ 2147483647
abbrev QA_WQ (q : AspisR1Qm31ArithmeticProbe.field.QM31) : Prop := QA_WC q.c0 ∧ QA_WC q.c1

theorem QA_M31_double_weak (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.M31.double x = ok z ∧ z.val ≤ 2147483647 := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.double; rw [QA_M31_add_eq]; exact refAdd_weak x x hx hx

theorem QA_CM31_add_weak (a b : AspisR1Qm31ArithmeticProbe.field.CM31) (ha : QA_WC a) (hb : QA_WC b) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.CM31.add a b = ok z ∧ QA_WC z := by
  obtain ⟨m, hm, vm⟩ := refAdd_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refAdd_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1Qm31ArithmeticProbe.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.add, QA_M31_add_eq, hm, hm1, bind_tc_ok]

theorem QA_CM31_sub_weak (a b : AspisR1Qm31ArithmeticProbe.field.CM31) (ha : QA_WC a) (hb : QA_WC b) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.CM31.sub a b = ok z ∧ QA_WC z := by
  obtain ⟨m, hm, vm⟩ := refSub_weak a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak a.b b.b ha.2 hb.2
  refine ⟨({ a := m, b := m1 } : AspisR1Qm31ArithmeticProbe.field.CM31), ?_, vm, vm1⟩
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.sub, QA_M31_sub_eq, hm, hm1, bind_tc_ok]

theorem QA_mul_by_r_weak (x : AspisR1Qm31ArithmeticProbe.field.CM31) (hx : QA_WC x) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.mul_by_r x = ok z ∧ QA_WC z := by
  obtain ⟨m, hm, vm⟩ := QA_M31_double_weak x.a hx.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak m x.b vm hx.2
  obtain ⟨m2, hm2, vm2⟩ := QA_M31_double_weak x.b hx.2
  obtain ⟨m3, hm3, vm3⟩ := refAdd_weak x.a m2 hx.1 vm2
  refine ⟨({ a := m1, b := m3 } : AspisR1Qm31ArithmeticProbe.field.CM31), ?_, vm1, vm3⟩
  simp only [AspisR1Qm31ArithmeticProbe.field.mul_by_r, QA_M31_sub_eq, QA_M31_add_eq, hm, hm1, hm2, hm3, bind_tc_ok]

theorem QA_QM31_add_weak (a b : AspisR1Qm31ArithmeticProbe.field.QM31) (ha : QA_WQ a) (hb : QA_WQ b) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.QM31.add a b = ok z ∧ QA_WQ z := by
  obtain ⟨c, hc, vc⟩ := QA_CM31_add_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := QA_CM31_add_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({ c0 := c, c1 := c1 } : AspisR1Qm31ArithmeticProbe.field.QM31), ?_, vc, vc1⟩
  simp only [AspisR1Qm31ArithmeticProbe.field.QM31.add, hc, hc1, bind_tc_ok]

theorem QA_QM31_mul_weak (a b : AspisR1Qm31ArithmeticProbe.field.QM31) (ha : QA_WQ a) (hb : QA_WQ b) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.QM31.mul a b = ok z ∧ QA_WQ z := by
  obtain ⟨m0, h0, v0a, v0b⟩ := QA_CM31_mul_weak a.c0 b.c0 ha.1.1 ha.1.2 hb.1.1 hb.1.2
  obtain ⟨m1, h1, v1a, v1b⟩ := QA_CM31_mul_weak a.c1 b.c1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  obtain ⟨c, hc, vc⟩ := QA_CM31_add_weak a.c0 a.c1 ha.1 ha.2
  obtain ⟨c1, hc1, vc1⟩ := QA_CM31_add_weak b.c0 b.c1 hb.1 hb.2
  obtain ⟨m2, h2, v2a, v2b⟩ := QA_CM31_mul_weak c c1 vc.1 vc.2 vc1.1 vc1.2
  obtain ⟨c2, hc2, vc2⟩ := QA_mul_by_r_weak m1 ⟨v1a, v1b⟩
  obtain ⟨c3, hc3, vc3⟩ := QA_CM31_add_weak m0 c2 ⟨v0a, v0b⟩ vc2
  obtain ⟨c4, hc4, vc4⟩ := QA_CM31_sub_weak m2 m0 ⟨v2a, v2b⟩ ⟨v0a, v0b⟩
  obtain ⟨c5, hc5, vc5⟩ := QA_CM31_sub_weak c4 m1 vc4 ⟨v1a, v1b⟩
  refine ⟨({ c0 := c3, c1 := c5 } : AspisR1Qm31ArithmeticProbe.field.QM31), ?_, vc3, vc5⟩
  simp only [AspisR1Qm31ArithmeticProbe.field.QM31.mul, h0, h1, hc, hc1, h2, hc2, hc3, hc4, hc5, bind_tc_ok]

#print axioms value_lt
#print axioms decodeK_strict_limbs_lt
#print axioms s8_strict_limbs_lt
#print axioms CW_M31_double_weak
#print axioms CW_CM31_add_weak
#print axioms CW_CM31_sub_weak
#print axioms CW_mul_by_r_weak
#print axioms CW_QM31_add_weak
#print axioms CW_QM31_mul_weak
#print axioms CW_QM31_sub_weak
#print axioms QA_M31_double_weak
#print axioms QA_CM31_add_weak
#print axioms QA_CM31_sub_weak
#print axioms QA_mul_by_r_weak
#print axioms QA_QM31_add_weak
#print axioms QA_QM31_mul_weak
end AspisR1.NPH_R22Producers
