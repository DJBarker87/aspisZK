import V7CallerCurrentReleaseR20.Funs
import CM31MultiplicativeProof
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Ring

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseFieldBridge

abbrev M31 := V7CallerCurrentReleaseR20.field.M31
abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31

/-! ## Exact semantics of the generated QM31 operations

This bridge uses the single source-authentic multiplicative extraction already
proved in `CM31MultiplicativeProof`.  The generated MLE module owns distinct
CM31/QM31 structures, so the bridge is explicit at every coordinate; the M31
words themselves are definitionally the same `U32` type.
-/

abbrev GeneratedCM31 := V7CallerCurrentReleaseR20.field.CM31
abbrev ExactM31 := AspisAeneasCM31Exact.M31Exact
abbrev ExactCM31 := AspisAeneasCM31Exact.CM31Exact

def exactQm31R : ExactCM31 := ⟨2, 1⟩

abbrev ExactQM31 := QuadraticAlgebra ExactCM31 exactQm31R 0

def generatedCm31ToExact (x : GeneratedCM31) : ExactCM31 :=
  ⟨(x.a.val : ExactM31), (x.b.val : ExactM31)⟩

def generatedQm31ToExact (x : QM31) : ExactQM31 :=
  ⟨generatedCm31ToExact x.c0, generatedCm31ToExact x.c1⟩

def GeneratedCanonicalCM31 (x : GeneratedCM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 x.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 x.b.val

def GeneratedCanonicalQM31 (x : QM31) : Prop :=
  GeneratedCanonicalCM31 x.c0 ∧ GeneratedCanonicalCM31 x.c1

private theorem generated_P_eq_multiplicative :
    V7CallerCurrentReleaseR20.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V7CallerCurrentReleaseR20.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem generated_reduce_u64_eq_multiplicative (x : Std.U64) :
    V7CallerCurrentReleaseR20.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold V7CallerCurrentReleaseR20.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [generated_P_eq_multiplicative]

private theorem generated_reduce_u64_eq_reference (x : Std.U64) :
    V7CallerCurrentReleaseR20.field.reduce_u64 x =
      aspis_core.field.reduce_u64 x := by
  have hP : V7CallerCurrentReleaseR20.field.P = aspis_core.field.P := by
    apply UScalar.eq_of_val_eq
    unfold V7CallerCurrentReleaseR20.field.P aspis_core.field.P
    rfl
  unfold V7CallerCurrentReleaseR20.field.reduce_u64 aspis_core.field.reduce_u64
  rw [hP]

private theorem generated_m31_reduce_u64_from_reference
    (x : Std.U64) (out : M31)
    (h : aspis_core.field.reduce_u64 x = ok out) :
    V7CallerCurrentReleaseR20.field.M31.reduce_u64 x = ok out := by
  simp [V7CallerCurrentReleaseR20.field.M31.reduce_u64,
    generated_reduce_u64_eq_reference, h]

@[simp] private theorem from_u64_u32_eq_cast (x : Std.U32) :
    core.convert.num.FromU64U32.from x = UScalar.cast .U64 x := by
  apply UScalar.eq_of_val_eq
  simp [core.convert.num.FromU64U32.from_val_eq]

private theorem generated_m31_add_eq_multiplicative (a b : M31) :
    V7CallerCurrentReleaseR20.field.M31.add a b =
      AspisCoreCM31Multiplicative.field.M31.add a b := by
  unfold V7CallerCurrentReleaseR20.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_sub_eq_multiplicative (a b : M31) :
    V7CallerCurrentReleaseR20.field.M31.sub a b =
      AspisCoreCM31Multiplicative.field.M31.sub a b := by
  unfold V7CallerCurrentReleaseR20.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_mul_eq_multiplicative (a b : M31) :
    V7CallerCurrentReleaseR20.field.M31.mul a b =
      AspisCoreCM31Multiplicative.field.M31.mul a b := by
  unfold V7CallerCurrentReleaseR20.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [generated_reduce_u64_eq_multiplicative]

private theorem generated_m31_add_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      V7CallerCurrentReleaseR20.field.M31.add a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) + (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_add_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_sub_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      V7CallerCurrentReleaseR20.field.M31.sub a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) - (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_sub_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_mul_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      V7CallerCurrentReleaseR20.field.M31.mul a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) * (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_mul_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_double_corresponds
    (a : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val) :
    ∃ out : M31,
      V7CallerCurrentReleaseR20.field.M31.double a = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) + (a.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    generated_m31_add_corresponds a a ha ha
  exact ⟨out, outputEquation, outputCanonical, outputExact⟩

private theorem generated_reduce_sum_product_corresponds
    (a b c d : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val)
    (hc : AspisAeneasCM31Multiplicative.CanonicalRawM31 c.val)
    (hd : AspisAeneasCM31Multiplicative.CanonicalRawM31 d.val) :
    ∃ out : M31,
      V7CallerCurrentReleaseR20.field.M31.reduce_u64
          (Std.U64.wrapping_mul
            (Std.U64.wrapping_add (UScalar.cast .U64 a) (UScalar.cast .U64 b))
            (Std.U64.wrapping_add (UScalar.cast .U64 c) (UScalar.cast .U64 d))) =
        ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        ((a.val : ExactM31) + (b.val : ExactM31)) *
          ((c.val : ExactM31) + (d.val : ExactM31)) := by
  let left := Std.U64.wrapping_add
    (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  let right := Std.U64.wrapping_add
    (UScalar.cast .U64 c) (UScalar.cast .U64 d)
  let product := Std.U64.wrapping_mul left right
  have hab32 : a.val + b.val < 2 ^ 32 := by
    unfold AspisAeneasCM31Multiplicative.CanonicalRawM31 at ha hb
    norm_num at ha hb ⊢
    omega
  have hcd32 : c.val + d.val < 2 ^ 32 := by
    unfold AspisAeneasCM31Multiplicative.CanonicalRawM31 at hc hd
    norm_num at hc hd ⊢
    omega
  have hleft : left.val = a.val + b.val := by
    simp only [left, Std.U64.wrapping_add_val_eq, U32.cast_U64_val_eq]
    rw [AspisAeneasM31ReduceU64.u64_size_eq]
    apply Nat.mod_eq_of_lt
    simpa [AspisAeneasM31ReduceU64.u64Cardinality] using
      (lt_trans hab32 (by norm_num : 2 ^ 32 < 2 ^ 64))
  have hright : right.val = c.val + d.val := by
    simp only [right, Std.U64.wrapping_add_val_eq, U32.cast_U64_val_eq]
    rw [AspisAeneasM31ReduceU64.u64_size_eq]
    apply Nat.mod_eq_of_lt
    simpa [AspisAeneasM31ReduceU64.u64Cardinality] using
      (lt_trans hcd32 (by norm_num : 2 ^ 32 < 2 ^ 64))
  have hproductBound : (a.val + b.val) * (c.val + d.val) < 2 ^ 64 := by
    by_cases hz : c.val + d.val = 0
    · simp [hz]
    · have h1 := Nat.mul_lt_mul_of_pos_right hab32 (Nat.pos_of_ne_zero hz)
      have h2 := Nat.mul_lt_mul_of_pos_left hcd32 (by norm_num : 0 < 2 ^ 32)
      norm_num at h1 h2 ⊢
      exact lt_trans h1 h2
  have hproduct : product.val = (a.val + b.val) * (c.val + d.val) := by
    simp only [product, Std.U64.wrapping_mul_val_eq, hleft, hright]
    rw [AspisAeneasM31ReduceU64.u64_size_eq]
    simpa [AspisAeneasM31ReduceU64.u64Cardinality] using
      Nat.mod_eq_of_lt hproductBound
  obtain ⟨out, hreduce, _hraw, hcanonical, hexact⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds product
  refine ⟨out, ?_, hcanonical, ?_⟩
  · apply generated_m31_reduce_u64_from_reference
    simpa [product, left, right] using hreduce
  · rw [hexact, hproduct, Nat.cast_mul, Nat.cast_add, Nat.cast_add]

private theorem generated_cm31_add_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      V7CallerCurrentReleaseR20.field.CM31.add x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x + generatedCm31ToExact y := by
  obtain ⟨oa, hcallA, hcanA, hexactA⟩ :=
    generated_m31_add_corresponds x.a y.a hx.1 hy.1
  obtain ⟨ob, hcallB, hcanB, hexactB⟩ :=
    generated_m31_add_corresponds x.b y.b hx.2 hy.2
  let out : GeneratedCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.CM31.add, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem generated_cm31_sub_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      V7CallerCurrentReleaseR20.field.CM31.sub x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x - generatedCm31ToExact y := by
  obtain ⟨oa, hcallA, hcanA, hexactA⟩ :=
    generated_m31_sub_corresponds x.a y.a hx.1 hy.1
  obtain ⟨ob, hcallB, hcanB, hexactB⟩ :=
    generated_m31_sub_corresponds x.b y.b hx.2 hy.2
  let out : GeneratedCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.CM31.sub, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem generated_cm31_mul_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      V7CallerCurrentReleaseR20.field.CM31.mul x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x * generatedCm31ToExact y := by
  obtain ⟨m0, hm0, hm0Canonical, hm0Exact⟩ :=
    generated_m31_mul_corresponds x.a y.a hx.1 hy.1
  obtain ⟨m1, hm1, hm1Canonical, hm1Exact⟩ :=
    generated_m31_mul_corresponds x.b y.b hx.2 hy.2
  obtain ⟨m2, hm2, hm2Canonical, hm2Exact⟩ :=
    generated_reduce_sum_product_corresponds
      x.a x.b y.a y.b hx.1 hx.2 hy.1 hy.2
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_m31_sub_corresponds m0 m1 hm0Canonical hm1Canonical
  obtain ⟨imagPartial, himagPartial, himagPartialCanonical,
      himagPartialExact⟩ :=
    generated_m31_sub_corresponds m2 m0 hm2Canonical hm0Canonical
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_sub_corresponds imagPartial m1
      himagPartialCanonical hm1Canonical
  have realExact :
      ((real.val : Nat) : ExactM31) =
        (x.a.val : ExactM31) * (y.a.val : ExactM31) -
          (x.b.val : ExactM31) * (y.b.val : ExactM31) := by
    rw [hrealExact, hm0Exact, hm1Exact]
  have imagExact :
      ((imag.val : Nat) : ExactM31) =
        (x.a.val : ExactM31) * (y.b.val : ExactM31) +
          (x.b.val : ExactM31) * (y.a.val : ExactM31) := by
    calc
      ((imag.val : Nat) : ExactM31) =
          ((imagPartial.val : Nat) : ExactM31) -
            ((m1.val : Nat) : ExactM31) := himagExact
      _ = (((m2.val : Nat) : ExactM31) -
            ((m0.val : Nat) : ExactM31)) -
            ((m1.val : Nat) : ExactM31) := by rw [himagPartialExact]
      _ = (((x.a.val : ExactM31) + (x.b.val : ExactM31)) *
            ((y.a.val : ExactM31) + (y.b.val : ExactM31)) -
            (x.a.val : ExactM31) * (y.a.val : ExactM31)) -
            (x.b.val : ExactM31) * (y.b.val : ExactM31) := by
          rw [hm2Exact, hm0Exact, hm1Exact]
      _ = (x.a.val : ExactM31) * (y.b.val : ExactM31) +
            (x.b.val : ExactM31) * (y.a.val : ExactM31) := by ring
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.CM31.mul, Std.lift, bind_tc_ok, hm0, hm1,
      from_u64_u32_eq_cast, hm2, hreal, himagPartial, himag, out]
  · apply QuadraticAlgebra.ext
    · simpa [generatedCm31ToExact, sub_eq_add_neg] using realExact
    · simpa [generatedCm31ToExact] using imagExact

private theorem generated_mul_by_r_corresponds
    (x : GeneratedCM31) (hx : GeneratedCanonicalCM31 x) :
    ∃ out : GeneratedCM31,
      V7CallerCurrentReleaseR20.field.mul_by_r x = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = generatedCm31ToExact x * exactQm31R := by
  obtain ⟨doubleA, hdoubleA, hdoubleACanonical, hdoubleAExact⟩ :=
    generated_m31_add_corresponds x.a x.a hx.1 hx.1
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_m31_sub_corresponds doubleA x.b hdoubleACanonical hx.2
  obtain ⟨doubleB, hdoubleB, hdoubleBCanonical, hdoubleBExact⟩ :=
    generated_m31_add_corresponds x.b x.b hx.2 hx.2
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_add_corresponds x.a doubleB hx.1 hdoubleBCanonical
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.mul_by_r,
      V7CallerCurrentReleaseR20.field.M31.double,
      hdoubleA, hreal, hdoubleB, himag, out]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (generatedCm31ToExact x * exactQm31R).re
      rw [hrealExact, hdoubleAExact]
      simp [generatedCm31ToExact, exactQm31R]
      ring
    · change ((imag.val : Nat) : ExactM31) =
        (generatedCm31ToExact x * exactQm31R).im
      rw [himagExact, hdoubleBExact]
      simp [generatedCm31ToExact, exactQm31R]
      ring

theorem generated_qm31_add_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      V7CallerCurrentReleaseR20.field.QM31.add x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x + generatedQm31ToExact y := by
  obtain ⟨o0, hcall0, hcan0, hexact0⟩ :=
    generated_cm31_add_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨o1, hcall1, hcan1, hexact1⟩ :=
    generated_cm31_add_corresponds x.c1 y.c1 hx.2 hy.2
  let out : QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.QM31.add, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem generated_qm31_sub_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      V7CallerCurrentReleaseR20.field.QM31.sub x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x - generatedQm31ToExact y := by
  obtain ⟨o0, hcall0, hcan0, hexact0⟩ :=
    generated_cm31_sub_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨o1, hcall1, hcan1, hexact1⟩ :=
    generated_cm31_sub_corresponds x.c1 y.c1 hx.2 hy.2
  let out : QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.QM31.sub, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem generated_qm31_mul_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      V7CallerCurrentReleaseR20.field.QM31.mul x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x * generatedQm31ToExact y := by
  obtain ⟨m0, hm0, hm0Canonical, hm0Exact⟩ :=
    generated_cm31_mul_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨m1, hm1, hm1Canonical, hm1Exact⟩ :=
    generated_cm31_mul_corresponds x.c1 y.c1 hx.2 hy.2
  obtain ⟨xsum, hxsum, hxsumCanonical, hxsumExact⟩ :=
    generated_cm31_add_corresponds x.c0 x.c1 hx.1 hx.2
  obtain ⟨ysum, hysum, hysumCanonical, hysumExact⟩ :=
    generated_cm31_add_corresponds y.c0 y.c1 hy.1 hy.2
  obtain ⟨m2, hm2, hm2Canonical, hm2Exact⟩ :=
    generated_cm31_mul_corresponds xsum ysum hxsumCanonical hysumCanonical
  obtain ⟨rm1, hrm1, hrm1Canonical, hrm1Exact⟩ :=
    generated_mul_by_r_corresponds m1 hm1Canonical
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_cm31_add_corresponds m0 rm1 hm0Canonical hrm1Canonical
  obtain ⟨crossPartial, hcrossPartial, hcrossPartialCanonical,
      hcrossPartialExact⟩ :=
    generated_cm31_sub_corresponds m2 m0 hm2Canonical hm0Canonical
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_cm31_sub_corresponds crossPartial m1
      hcrossPartialCanonical hm1Canonical
  let out : QM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.QM31.mul, hm0, hm1,
      hxsum, hysum, hm2, hrm1, hreal, hcrossPartial, himag, out]
  · apply QuadraticAlgebra.ext
    · change generatedCm31ToExact real =
        (generatedQm31ToExact x * generatedQm31ToExact y).re
      rw [hrealExact, hm0Exact, hrm1Exact, hm1Exact]
      simp [generatedQm31ToExact]
      ring
    · change generatedCm31ToExact imag =
        (generatedQm31ToExact x * generatedQm31ToExact y).im
      rw [himagExact, hcrossPartialExact, hm2Exact, hxsumExact,
        hysumExact, hm0Exact, hm1Exact]
      simp [generatedQm31ToExact]
      ring

private theorem generated_cm31_square_corresponds
    (x : GeneratedCM31) (hx : GeneratedCanonicalCM31 x) :
    ∃ out : GeneratedCM31,
      V7CallerCurrentReleaseR20.field.CM31.square x = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = generatedCm31ToExact x ^ 2 := by
  let wideA : Std.U64 := UScalar.cast .U64 x.a
  let wideB : Std.U64 := UScalar.cast .U64 x.b
  let wideP : Std.U64 := UScalar.cast .U64 V7CallerCurrentReleaseR20.field.P
  let wideSum := Std.U64.wrapping_add wideA wideB
  let wideDiff := Std.U64.wrapping_sub
    (Std.U64.wrapping_add wideA wideP) wideB
  let wideProduct := Std.U64.wrapping_mul wideSum wideDiff
  have hPval : V7CallerCurrentReleaseR20.field.P.val = 2147483647 := by
    simp [V7CallerCurrentReleaseR20.field.P]
  have hWideA : wideA.val = x.a.val := by
    simp [wideA, U32.cast_U64_val_eq]
  have hWideB : wideB.val = x.b.val := by
    simp [wideB, U32.cast_U64_val_eq]
  have hWideP : wideP.val = 2147483647 := by
    simp [wideP, U32.cast_U64_val_eq, hPval]
  have hSumBound : x.a.val + x.b.val < 2 ^ 64 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at hx
    norm_num at hx ⊢
    omega
  have hWideSum : wideSum.val = x.a.val + x.b.val := by
    simp only [wideSum, Std.U64.wrapping_add_val_eq,
      AspisAeneasM31ReduceU64.u64_size_eq, hWideA, hWideB,
      Nat.mod_eq_of_lt hSumBound]
  have hAddPBound : x.a.val + 2147483647 < 2 ^ 64 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at hx
    norm_num at hx ⊢
    omega
  have hAddP : (Std.U64.wrapping_add wideA wideP).val =
      x.a.val + 2147483647 := by
    rw [Std.U64.wrapping_add_val_eq,
      AspisAeneasM31ReduceU64.u64_size_eq, hWideA, hWideP,
      Nat.mod_eq_of_lt hAddPBound]
  have hbLe : x.b.val ≤ x.a.val + 2147483647 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at hx
    norm_num at hx ⊢
    omega
  have hDiffBound : x.a.val + 2147483647 - x.b.val < 2 ^ 64 := by
    omega
  have hWideDiff : wideDiff.val = x.a.val + 2147483647 - x.b.val := by
    simp only [wideDiff, Std.U64.wrapping_sub_val_eq,
      AspisAeneasM31ReduceU64.u64_size_eq, hAddP]
    have hrewrite :
        x.a.val + 2147483647 + (2 ^ 64 - x.b.val) =
          (x.a.val + 2147483647 - x.b.val) + 2 ^ 64 := by
      have hb64 : x.b.val ≤ 2 ^ 64 := by
        unfold GeneratedCanonicalCM31
          AspisAeneasCM31Multiplicative.CanonicalRawM31 at hx
        norm_num at hx ⊢
        omega
      omega
    change (x.a.val + 2147483647 + (2 ^ 64 - x.b.val)) % (2 ^ 64) = _
    rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hDiffBound]
  have hSum32 : x.a.val + x.b.val < 2 ^ 32 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at hx
    norm_num at hx ⊢
    omega
  have hDiff32 : x.a.val + 2147483647 - x.b.val < 2 ^ 32 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at hx
    norm_num at hx ⊢
    omega
  have hProductBound :
      (x.a.val + x.b.val) * (x.a.val + 2147483647 - x.b.val) <
        2 ^ 64 := by
    by_cases hz : x.a.val + 2147483647 - x.b.val = 0
    · simp [hz]
    · have h1 := Nat.mul_lt_mul_of_pos_right hSum32 (Nat.pos_of_ne_zero hz)
      have h2 := Nat.mul_lt_mul_of_pos_left hDiff32 (by norm_num : 0 < 2 ^ 32)
      norm_num at h1 h2 ⊢
      exact lt_trans h1 h2
  have hWideProduct : wideProduct.val =
      (x.a.val + x.b.val) * (x.a.val + 2147483647 - x.b.val) := by
    simp only [wideProduct, Std.U64.wrapping_mul_val_eq, hWideSum, hWideDiff]
    rw [AspisAeneasM31ReduceU64.u64_size_eq]
    simpa [AspisAeneasM31ReduceU64.u64Cardinality] using
      Nat.mod_eq_of_lt hProductBound
  obtain ⟨real, hreal, _hrealRaw, hrealCanonical, hrealExactWide⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds wideProduct
  have hrealCurrent :
      V7CallerCurrentReleaseR20.field.M31.reduce_u64 wideProduct = ok real :=
    generated_m31_reduce_u64_from_reference wideProduct real hreal
  have hrealExact : ((real.val : Nat) : ExactM31) =
      ((x.a.val : Nat) : ExactM31) ^ 2 -
        ((x.b.val : Nat) : ExactM31) ^ 2 := by
    rw [hrealExactWide, hWideProduct, Nat.cast_mul, Nat.cast_sub hbLe,
      Nat.cast_add, Nat.cast_add]
    have hp : ((2147483647 : Nat) : ExactM31) = 0 := by
      exact ZMod.natCast_self 2147483647
    rw [hp]
    ring
  obtain ⟨product, hproduct, hproductCanonical, hproductExact⟩ :=
    generated_m31_mul_corresponds x.a x.b hx.1 hx.2
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_double_corresponds product hproductCanonical
  have himagAdd :
      V7CallerCurrentReleaseR20.field.M31.add product product = ok imag := by
    simpa [V7CallerCurrentReleaseR20.field.M31.double] using himag
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.CM31.square, Std.lift, bind_tc_ok,
      wideA, wideB, wideP,
      wideSum, wideDiff, wideProduct, hrealCurrent,
      from_u64_u32_eq_cast, V7CallerCurrentReleaseR20.field.M31.double,
      hproduct, himagAdd, out]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (generatedCm31ToExact x ^ 2).re
      rw [hrealExact]
      simp [pow_two, generatedCm31ToExact]
      ring
    · change ((imag.val : Nat) : ExactM31) =
        (generatedCm31ToExact x ^ 2).im
      rw [himagExact, hproductExact]
      simp [pow_two, generatedCm31ToExact]
      ring

/-- The specialized square body in the authentic combined evaluator
extraction preserves canonical limbs and denotes exact squaring. -/
theorem generated_qm31_square_corresponds
    (x : QM31) (hx : GeneratedCanonicalQM31 x) :
    ∃ out : QM31,
      V7CallerCurrentReleaseR20.field.QM31.square x = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = generatedQm31ToExact x ^ 2 := by
  obtain ⟨c0Square, hc0Square, hc0SquareCanonical, hc0SquareExact⟩ :=
    generated_cm31_square_corresponds x.c0 hx.1
  obtain ⟨c1Square, hc1Square, hc1SquareCanonical, hc1SquareExact⟩ :=
    generated_cm31_square_corresponds x.c1 hx.2
  obtain ⟨rTimesC1Square, hrTimesC1Square, hrTimesC1SquareCanonical,
      hrTimesC1SquareExact⟩ :=
    generated_mul_by_r_corresponds c1Square hc1SquareCanonical
  obtain ⟨low, hlow, hlowCanonical, hlowExact⟩ :=
    generated_cm31_add_corresponds c0Square rTimesC1Square
      hc0SquareCanonical hrTimesC1SquareCanonical
  obtain ⟨cross, hcross, hcrossCanonical, hcrossExact⟩ :=
    generated_cm31_mul_corresponds x.c0 x.c1 hx.1 hx.2
  obtain ⟨high, hhigh, hhighCanonical, hhighExact⟩ :=
    generated_cm31_add_corresponds cross cross hcrossCanonical hcrossCanonical
  let out : QM31 := ⟨low, high⟩
  refine ⟨out, ?_, ⟨hlowCanonical, hhighCanonical⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.QM31.square,
      V7CallerCurrentReleaseR20.field.CM31.double, hc0Square,
      hc1Square, hrTimesC1Square, hlow, hcross, hhigh, out]
  · apply QuadraticAlgebra.ext
    · change generatedCm31ToExact low =
        (generatedQm31ToExact x ^ 2).re
      rw [hlowExact, hc0SquareExact, hrTimesC1SquareExact,
        hc1SquareExact]
      simp only [pow_two, QuadraticAlgebra.re_mul, generatedQm31ToExact]
      ring
    · change generatedCm31ToExact high =
        (generatedQm31ToExact x ^ 2).im
      rw [hhighExact, hcrossExact]
      simp [pow_two, generatedQm31ToExact]
      ring

#print axioms generated_qm31_add_corresponds
#print axioms generated_qm31_sub_corresponds
#print axioms generated_qm31_mul_corresponds
#print axioms generated_qm31_square_corresponds

end V7CallerCurrentReleaseFieldBridge
