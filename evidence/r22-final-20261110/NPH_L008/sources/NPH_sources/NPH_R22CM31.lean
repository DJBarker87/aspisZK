import NPH_R22FieldCopies
import AspisR1CanonicalQRawUnified.Funs
import FIo_QRawFuns
import AspisR1TerminalDecoder.Funs
import NFY_Part043

/-! NPH_ (R22 re-pin): CM31 multiplication/squaring copies reached by deployed_splitB with
checked bodies. Domain: canonical limbs (< P) on both operands, which is the output
invariant of every M31 kernel above (each returns a canonical limb). Conclusion: checked
success with canonical output limbs. The CM31 bodies contain one widened U64 add/add/mul
(the Karatsuba cross term, bounded by (2P-2)^2 < 2^64) and calls to the M31 kernels already
handled in NPH_R22FieldCopies. Also: the three wrapping-tail closure bodies of the mixed
class and the two transition_kind decoders, TOTAL for every input. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22CM31
open Aeneas Aeneas.Std Result AspisR1.R22TotalCheckedComposition AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies

theorem from_val (u : U32) : (core.convert.num.FromU64U32.from u).val = u.val := by
  first
  | rfl
  | (simp [core.convert.num.FromU64U32.from]; done)
  | (unfold core.convert.num.FromU64U32.from; exact cast64_val u)
  | (simp only [core.convert.num.FromU64U32.from]; exact cast64_val u)

/-- The cross-term product used by both CM31 bodies; R72's guarded helper as well. -/
theorem cross_ok (l r : U64) (hl : l.val ≤ 4294967292) (hr : r.val ≤ 4294967293) :
    ∃ z, (l * r : Result U64) = ok z ∧ z.val = l.val * r.val := by
  have hm : l.val * r.val ≤ 4294967292 * 4294967293 := Nat.mul_le_mul hl hr
  exact mul_ok l r (by rw [max64]; omega)

theorem CW_reduce_wrapper (v : U64) : AspisR1CurrentWide.field.M31.reduce_u64 v = refReduce v := by
  unfold AspisR1CurrentWide.field.M31.reduce_u64
  rw [CW_reduce_u64_eq]
  cases refReduce v <;> rfl

theorem QA_reduce_wrapper (v : U64) : AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 v = refReduce v := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
  rw [QA_reduce_u64_eq]
  cases refReduce v <;> rfl

theorem SM_reduce_wrapper (v : U64) : AspisR1SelectedMaskProbe.field.M31.reduce_u64 v = refReduce v := by
  unfold AspisR1SelectedMaskProbe.field.M31.reduce_u64
  rw [SM_reduce_u64_eq]
  cases refReduce v <;> rfl

theorem SC_reduce_wrapper (v : U64) : AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64 v = refReduce v := by
  unfold AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64
  rw [SC_reduce_u64_eq]
  cases refReduce v <;> rfl

theorem FIq_reduce_wrapper (v : U64) : FIq_Native.field.M31.reduce_u64 v = refReduce v := by
  unfold FIq_Native.field.M31.reduce_u64
  rw [FIq_reduce_u64_eq]
  cases refReduce v <;> rfl

theorem R72_reduce_wrapper (v : U64) : AspisR72Sampler.field.M31.reduce_u64 v = refReduce v := by
  unfold AspisR72Sampler.field.M31.reduce_u64
  rw [R72_reduce_u64_eq]
  cases refReduce v <;> rfl

theorem r23_total (l r : U64) (hl : l.val ≤ 4294967292) (hr : r.val ≤ 4294967293) :
    ∃ z, AspisR72Sampler.field.r23_product_u32_bounded l r = ok z ∧ z.val = l.val * r.val := by
  have hl32 := cast32_val l (by omega)
  have hr32 := cast32_val r (by omega)
  obtain ⟨z, hz, hv⟩ := cross_ok l r hl hr
  obtain ⟨z2, hz2, hv2⟩ := cross_ok (core.convert.num.FromU64U32.from (UScalar.cast .U32 l))
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

theorem CW_CM31_mul_total (a b : AspisR1CurrentWide.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647)
    (hc : b.a.val < 2147483647) (hd : b.b.val < 2147483647) :
    ∃ z, AspisR1CurrentWide.field.CM31.mul a b = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_ok i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm, _⟩ := refSub_total m0 m1 v0 v1
  obtain ⟨m3, hm3, vm3, _⟩ := refSub_total m2 m0 vm2 v0
  obtain ⟨m4, hm4, vm4, _⟩ := refSub_total m3 m1 vm3 v1
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1CurrentWide.field.CM31.mul, CW_M31_mul_eq, CW_M31_sub_eq, CW_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem QA_CM31_mul_total (a b : AspisR1Qm31ArithmeticProbe.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647)
    (hc : b.a.val < 2147483647) (hd : b.b.val < 2147483647) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.CM31.mul a b = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_ok i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm, _⟩ := refSub_total m0 m1 v0 v1
  obtain ⟨m3, hm3, vm3, _⟩ := refSub_total m2 m0 vm2 v0
  obtain ⟨m4, hm4, vm4, _⟩ := refSub_total m3 m1 vm3 v1
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.mul, QA_M31_mul_eq, QA_M31_sub_eq, QA_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem SM_CM31_mul_total (a b : AspisR1SelectedMaskProbe.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647)
    (hc : b.a.val < 2147483647) (hd : b.b.val < 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.mul a b = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_ok i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm, _⟩ := refSub_total m0 m1 v0 v1
  obtain ⟨m3, hm3, vm3, _⟩ := refSub_total m2 m0 vm2 v0
  obtain ⟨m4, hm4, vm4, _⟩ := refSub_total m3 m1 vm3 v1
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1SelectedMaskProbe.field.CM31.mul, SM_M31_mul_eq, SM_M31_sub_eq, SM_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem SC_CM31_mul_total (a b : AspisR1SemanticCallExtraction.aspis_core.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647)
    (hc : b.a.val < 2147483647) (hd : b.b.val < 2147483647) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul a b = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_ok i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm, _⟩ := refSub_total m0 m1 v0 v1
  obtain ⟨m3, hm3, vm3, _⟩ := refSub_total m2 m0 vm2 v0
  obtain ⟨m4, hm4, vm4, _⟩ := refSub_total m3 m1 vm3 v1
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul, SC_M31_mul_eq, SC_M31_sub_eq, SC_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem FIq_CM31_mul_total (a b : FIq_Native.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647)
    (hc : b.a.val < 2147483647) (hd : b.b.val < 2147483647) :
    ∃ z, FIq_Native.field.CM31.mul a b = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := refMul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := refMul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_ok i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm, _⟩ := refSub_total m0 m1 v0 v1
  obtain ⟨m3, hm3, vm3, _⟩ := refSub_total m2 m0 vm2 v0
  obtain ⟨m4, hm4, vm4, _⟩ := refSub_total m3 m1 vm3 v1
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [FIq_Native.field.CM31.mul, FIq_M31_mul_eq, FIq_M31_sub_eq, FIq_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem R72_CM31_mul_total (a b : AspisR72Sampler.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647)
    (hc : b.a.val < 2147483647) (hd : b.b.val < 2147483647) :
    ∃ z, AspisR72Sampler.field.CM31.mul a b = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  obtain ⟨m0, h0, v0⟩ := R72_M31_mul_total a.a b.a
  obtain ⟨m1, h1, v1⟩ := R72_M31_mul_total a.b b.b
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := add_ok (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i10, h10, v10⟩ := r23_total i4 i9 (by rw [v4, from_val, from_val]; omega) (by rw [v9, from_val, from_val]; omega)
  obtain ⟨m2, hm2, vm2⟩ := refReduce_total i10
  obtain ⟨m, hm, vm, _⟩ := refSub_total m0 m1 v0 v1
  obtain ⟨m3, hm3, vm3, _⟩ := refSub_total m2 m0 vm2 v0
  obtain ⟨m4, hm4, vm4, _⟩ := refSub_total m3 m1 vm3 v1
  refine ⟨{ a := m, b := m4 }, ?_, vm, vm4⟩
  simp only [AspisR72Sampler.field.CM31.mul, R72_M31_sub_eq, R72_reduce_wrapper, lift, bind_tc_ok, h0, h1, h4, h9, h10, hm2, hm, hm3, hm4]

theorem SM_double_eq : AspisR1SelectedMaskProbe.field.M31.double = fun x => refAdd x x := by
  funext x; unfold AspisR1SelectedMaskProbe.field.M31.double; rw [SM_M31_add_eq]

theorem SM_CM31_square_total (a : AspisR1SelectedMaskProbe.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.square a = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  have hPv : (AspisR1SelectedMaskProbe.field.P).val = 2147483647 := by unfold AspisR1SelectedMaskProbe.field.P; rfl
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i7, h7, v7⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from AspisR1SelectedMaskProbe.field.P)
    (by rw [from_val, from_val, hPv, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := sub_ok i7 (core.convert.num.FromU64U32.from a.b)
    (by rw [v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_ok i4 i9 (by rw [v4, from_val, from_val]; omega)
    (by rw [v9, v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨m, hm, vm⟩ := refReduce_total i10
  obtain ⟨m1, hm1, vm1⟩ := refMul_total a.a a.b
  obtain ⟨m2, hm2, vm2, _⟩ := refAdd_total m1 m1 vm1 vm1
  refine ⟨{ a := m, b := m2 }, ?_, vm, vm2⟩
  simp only [AspisR1SelectedMaskProbe.field.CM31.square, SM_M31_mul_eq, SM_double_eq, SM_reduce_wrapper, lift, bind_tc_ok, h4, h7, h9, h10, hm, hm1, hm2]

theorem FIq_double_eq : FIq_Native.field.M31.double = fun x => refAdd x x := by
  funext x; unfold FIq_Native.field.M31.double; rw [FIq_M31_add_eq]

theorem FIq_CM31_square_total (a : FIq_Native.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647) :
    ∃ z, FIq_Native.field.CM31.square a = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  have hPv : (FIq_Native.field.P).val = 2147483647 := by unfold FIq_Native.field.P; rfl
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i7, h7, v7⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from FIq_Native.field.P)
    (by rw [from_val, from_val, hPv, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := sub_ok i7 (core.convert.num.FromU64U32.from a.b)
    (by rw [v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨i10, h10, v10⟩ := cross_ok i4 i9 (by rw [v4, from_val, from_val]; omega)
    (by rw [v9, v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨m, hm, vm⟩ := refReduce_total i10
  obtain ⟨m1, hm1, vm1⟩ := refMul_total a.a a.b
  obtain ⟨m2, hm2, vm2, _⟩ := refAdd_total m1 m1 vm1 vm1
  refine ⟨{ a := m, b := m2 }, ?_, vm, vm2⟩
  simp only [FIq_Native.field.CM31.square, FIq_M31_mul_eq, FIq_double_eq, FIq_reduce_wrapper, lift, bind_tc_ok, h4, h7, h9, h10, hm, hm1, hm2]

theorem R72_double_eq : AspisR72Sampler.field.M31.double = fun x => refAdd x x := by
  funext x; unfold AspisR72Sampler.field.M31.double; rw [R72_M31_add_eq]

theorem R72_CM31_square_total (a : AspisR72Sampler.field.CM31)
    (ha : a.a.val < 2147483647) (hb : a.b.val < 2147483647) :
    ∃ z, AspisR72Sampler.field.CM31.square a = ok z ∧ z.a.val < 2147483647 ∧ z.b.val < 2147483647 := by
  have hPv : (AspisR72Sampler.field.P).val = 2147483647 := by unfold AspisR72Sampler.field.P; rfl
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i7, h7, v7⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from AspisR72Sampler.field.P)
    (by rw [from_val, from_val, hPv, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := sub_ok i7 (core.convert.num.FromU64U32.from a.b)
    (by rw [v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨i10, h10, v10⟩ := r23_total i4 i9 (by rw [v4, from_val, from_val]; omega)
    (by rw [v9, v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨m, hm, vm⟩ := refReduce_total i10
  obtain ⟨m1, hm1, vm1⟩ := R72_M31_mul_total a.a a.b
  obtain ⟨m2, hm2, vm2, _⟩ := refAdd_total m1 m1 vm1 vm1
  refine ⟨{ a := m, b := m2 }, ?_, vm, vm2⟩
  simp only [AspisR72Sampler.field.CM31.square, R72_double_eq, R72_reduce_wrapper, lift, bind_tc_ok, h4, h7, h9, h10, hm, hm1, hm2]

/-- TOTAL for every closure state and U64 argument (constant in-range i32 shift amount;
the final addition is Rust `wrapping_add`, modelled with its own semantics). -/
theorem R72_r24_closure_total (c : AspisR72Sampler.field.r24_canonical_mul.closure) (t : U64) : ∃ v, AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call c t = ok v := by
  obtain ⟨i2, h2, _⟩ := shr31i_val t
  simp only [AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call, lift, bind_tc_ok, h2]
  exact ⟨_, rfl⟩

/-- TOTAL for every closure state and U64 argument (constant in-range i32 shift amount;
the final addition is Rust `wrapping_add`, modelled with its own semantics). -/
theorem QRawU_closure2_total (c : AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2) (t : U64) : ∃ v, AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call c t = ok v := by
  obtain ⟨i2, h2, _⟩ := shr31i_val t
  simp only [AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call, lift, bind_tc_ok, h2]
  exact ⟨_, rfl⟩

/-- TOTAL for every closure state and U64 argument (constant in-range i32 shift amount;
the final addition is Rust `wrapping_add`, modelled with its own semantics). -/
theorem FIoQRaw_closure2_total (c : FIo_QRaw.canonical.Q.raw.closure_2) (t : U64) : ∃ v, FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call c t = ok v := by
  obtain ⟨i2, h2, _⟩ := shr31i_val t
  simp only [FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call, lift, bind_tc_ok, h2]
  exact ⟨_, rfl⟩

theorem max8 : UScalar.max .U8 = 255 := by
  simp only [UScalar.max, UScalarTy.numBits]; decide

theorem u8_add_lit (x y z : U8) (h : x.val + y.val = z.val) (hb : x.val + y.val ≤ UScalar.max .U8) :
    (x + y : Result U8) = ok z := by
  obtain ⟨w, hw, hv⟩ := add_ok x y hb
  have : w = z := UScalar.eq_of_val_eq (by omega)
  rw [hw, this]

/-- TOTAL for every byte (constant `1+0`, `2+0` checked additions). -/
theorem TD_transition_kind_total (byte : U8) : ∃ v, AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.transition_kind byte = ok v := by
  have h1 : (1#u8 + 0#u8 : Result U8) = ok 1#u8 := u8_add_lit _ _ _ (by decide) (by rw [max8]; decide)
  have h2 : (2#u8 + 0#u8 : Result U8) = ok 2#u8 := u8_add_lit _ _ _ (by decide) (by rw [max8]; decide)
  simp only [AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.transition_kind, h1, h2, lift, bind_tc_ok]
  split
  · exact ⟨_, rfl⟩
  · split <;> exact ⟨_, rfl⟩

/-- TOTAL for every byte (constant `1+0`, `2+0` checked additions). -/
theorem R20_transition_kind_total (byte : U8) : ∃ v, AspisR20Request.pool_v1.pair_forest_terminal.transition_kind byte = ok v := by
  have h1 : (1#u8 + 0#u8 : Result U8) = ok 1#u8 := u8_add_lit _ _ _ (by decide) (by rw [max8]; decide)
  have h2 : (2#u8 + 0#u8 : Result U8) = ok 2#u8 := u8_add_lit _ _ _ (by decide) (by rw [max8]; decide)
  simp only [AspisR20Request.pool_v1.pair_forest_terminal.transition_kind, h1, h2, lift, bind_tc_ok]
  split
  · exact ⟨_, rfl⟩
  · split <;> exact ⟨_, rfl⟩

#print axioms from_val
#print axioms cross_ok
#print axioms CW_reduce_wrapper
#print axioms QA_reduce_wrapper
#print axioms SM_reduce_wrapper
#print axioms SC_reduce_wrapper
#print axioms FIq_reduce_wrapper
#print axioms R72_reduce_wrapper
#print axioms r23_total
#print axioms CW_CM31_mul_total
#print axioms QA_CM31_mul_total
#print axioms SM_CM31_mul_total
#print axioms SC_CM31_mul_total
#print axioms FIq_CM31_mul_total
#print axioms R72_CM31_mul_total
#print axioms SM_double_eq
#print axioms SM_CM31_square_total
#print axioms FIq_double_eq
#print axioms FIq_CM31_square_total
#print axioms R72_double_eq
#print axioms R72_CM31_square_total
#print axioms R72_r24_closure_total
#print axioms QRawU_closure2_total
#print axioms FIoQRaw_closure2_total
#print axioms u8_add_lit
#print axioms TD_transition_kind_total
#print axioms R20_transition_kind_total
end AspisR1.NPH_R22CM31