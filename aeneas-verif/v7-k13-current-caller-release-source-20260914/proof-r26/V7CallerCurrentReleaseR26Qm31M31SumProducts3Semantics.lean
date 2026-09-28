import V7CallerCurrentReleaseR26Qm31DotRawArithmetic

/-!
# Exact current three-term QM31-by-M31 dot product

The line-batch fold uses a specialized three-term helper.  This proof keeps
the generated U64 arithmetic explicit and proves that no intermediate wraps
for canonical M31 inputs.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31M31SumProducts3Semantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawM31 := ⟨0#u32⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def CanonicalM31Array3 (values : Array RawM31 3#usize) : Prop :=
  ∀ index, index < 3 → GeneratedCanonicalM31 values.val[index]!

def CanonicalQM31Array3 (values : Array RawQM31 3#usize) : Prop :=
  ∀ index, index < 3 → GeneratedCanonicalQM31 values.val[index]!

def exactM31Dot3
    (a b c : RawM31) (right : Array RawM31 3#usize) : ExactM31 :=
  generatedM31ToExact a * generatedM31ToExact right.val[0]! +
    generatedM31ToExact b * generatedM31ToExact right.val[1]! +
    generatedM31ToExact c * generatedM31ToExact right.val[2]!

@[simp] private theorem generatedM31ToExact_eq_cast (value : RawM31) :
    generatedM31ToExact value = ((value.val : Nat) : ExactM31) := rfl

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have listEq : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, listEq] using run

private theorem threeProductsFit
    (a b c r0 r1 r2 : RawM31)
    (ha : GeneratedCanonicalM31 a) (hb : GeneratedCanonicalM31 b)
    (hc : GeneratedCanonicalM31 c)
    (hr0 : GeneratedCanonicalM31 r0)
    (hr1 : GeneratedCanonicalM31 r1)
    (hr2 : GeneratedCanonicalM31 r2) :
    rawM31Product a r0 + rawM31Product b r1 + rawM31Product c r2 <
      2 ^ 64 := by
  have h0 := canonical_m31_product_lt_two_pow_62 a r0 ha hr0
  have h1 := canonical_m31_product_lt_two_pow_62 b r1 hb hr1
  have h2 := canonical_m31_product_lt_two_pow_62 c r2 hc hr2
  norm_num at h0 h1 h2 ⊢
  omega

private theorem generatedThreeM31DotCorresponds
    (right : Array RawM31 3#usize) (a b c : RawM31)
    (hright : CanonicalM31Array3 right)
    (ha : GeneratedCanonicalM31 a)
    (hb : GeneratedCanonicalM31 b)
    (hc : GeneratedCanonicalM31 c) :
    ∃ out,
      field.qm31_m31_sum_products3.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
          right (a, b, c) = ok out ∧
      GeneratedCanonicalM31 out ∧
      generatedM31ToExact out = exactM31Dot3 a b c right := by
  let r0 := right.val[0]!
  let r1 := right.val[1]!
  let r2 := right.val[2]!
  have hr0 : GeneratedCanonicalM31 r0 := hright 0 (by omega)
  have hr1 : GeneratedCanonicalM31 r1 := hright 1 (by omega)
  have hr2 : GeneratedCanonicalM31 r2 := hright 2 (by omega)
  have read0 := arrayIndexRun right 0#usize (by decide)
  have read1 := arrayIndexRun right 1#usize (by decide)
  have read2 := arrayIndexRun right 2#usize (by decide)
  let p0 := Std.U64.wrapping_mul
    (UScalar.cast .U64 a) (UScalar.cast .U64 r0)
  let p1 := Std.U64.wrapping_mul
    (UScalar.cast .U64 b) (UScalar.cast .U64 r1)
  let p2 := Std.U64.wrapping_mul
    (UScalar.cast .U64 c) (UScalar.cast .U64 r2)
  have p0Exact : p0.val = rawM31Product a r0 := by
    exact wrapping_product_exact a r0 ha hr0
  have p1Exact : p1.val = rawM31Product b r1 := by
    exact wrapping_product_exact b r1 hb hr1
  have p2Exact : p2.val = rawM31Product c r2 := by
    exact wrapping_product_exact c r2 hc hr2
  let sum01 := Std.U64.wrapping_add p0 p1
  have sum01Bound : p0.val + rawM31Product b r1 < 2 ^ 64 := by
    rw [p0Exact]
    have fit := threeProductsFit a b c r0 r1 r2 ha hb hc hr0 hr1 hr2
    omega
  have sum01Exact : sum01.val =
      rawM31Product a r0 + rawM31Product b r1 := by
    unfold sum01 p1
    rw [wrapping_accumulate_exact p0 b r1 hb hr1 sum01Bound, p0Exact]
  let total := Std.U64.wrapping_add sum01 p2
  have totalBound : sum01.val + rawM31Product c r2 < 2 ^ 64 := by
    rw [sum01Exact]
    exact threeProductsFit a b c r0 r1 r2 ha hb hc hr0 hr1 hr2
  have totalExact : total.val =
      rawM31Product a r0 + rawM31Product b r1 +
        rawM31Product c r2 := by
    unfold total p2
    rw [wrapping_accumulate_exact sum01 c r2 hc hr2 totalBound,
      sum01Exact]
  obtain ⟨out, reduceRun, outCanonical, outExact⟩ :=
    generated_m31_reduce_u64_corresponds total
  refine ⟨out, ?_, outCanonical, ?_⟩
  · unfold
      field.qm31_m31_sum_products3.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
    simp only [Std.lift, bind_tc_ok]
    rw [read0, read1, read2]
    simpa [r0, r1, r2, p0, p1, p2, sum01, total] using reduceRun
  · rw [outExact, totalExact]
    simp [exactM31Dot3, rawM31Product, generatedM31ToExact, r0, r1, r2,
      Nat.cast_add, Nat.cast_mul]

def exactQm31M31Dot3
    (left : Array RawQM31 3#usize) (right : Array RawM31 3#usize) :
    ExactQM31 :=
  ∑ index ∈ Finset.range 3,
    generatedQm31ToExact left.val[index]! *
      generatedM31ScalarToExactQM31 right.val[index]!

/-- The public specialized helper is exactly the three-term dot product in
the extracted exact field. -/
theorem generated_qm31_m31_sum_products3_corresponds
    (left : Array RawQM31 3#usize) (right : Array RawM31 3#usize)
    (hleft : CanonicalQM31Array3 left)
    (hright : CanonicalM31Array3 right) :
    ∃ out,
      field.qm31_m31_sum_products3 left right = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = exactQm31M31Dot3 left right := by
  have leftRead0 := arrayIndexRun left 0#usize (by decide)
  have leftRead1 := arrayIndexRun left 1#usize (by decide)
  have leftRead2 := arrayIndexRun left 2#usize (by decide)
  let q0 := left.val[0]!
  let q1 := left.val[1]!
  let q2 := left.val[2]!
  have hq0 := hleft 0 (by omega)
  have hq1 := hleft 1 (by omega)
  have hq2 := hleft 2 (by omega)
  obtain ⟨o0, run0, can0, exact0⟩ := generatedThreeM31DotCorresponds
    right q0.c0.a q1.c0.a q2.c0.a hright hq0.1.1 hq1.1.1 hq2.1.1
  obtain ⟨o1, run1, can1, exact1⟩ := generatedThreeM31DotCorresponds
    right q0.c0.b q1.c0.b q2.c0.b hright hq0.1.2 hq1.1.2 hq2.1.2
  obtain ⟨o2, run2, can2, exact2⟩ := generatedThreeM31DotCorresponds
    right q0.c1.a q1.c1.a q2.c1.a hright hq0.2.1 hq1.2.1 hq2.2.1
  obtain ⟨o3, run3, can3, exact3⟩ := generatedThreeM31DotCorresponds
    right q0.c1.b q1.c1.b q2.c1.b hright hq0.2.2 hq1.2.2 hq2.2.2
  let out : RawQM31 := ⟨⟨o0, o1⟩, ⟨o2, o3⟩⟩
  refine ⟨out, ?_, ⟨⟨can0, can1⟩, ⟨can2, can3⟩⟩, ?_⟩
  · unfold field.qm31_m31_sum_products3
    rw [leftRead0, leftRead1, leftRead2]
    simp only [bind_tc_ok]
    change (do
      let m ←
        field.qm31_m31_sum_products3.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
          right (q0.c0.a, q1.c0.a, q2.c0.a)
      let m1 ←
        field.qm31_m31_sum_products3.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
          right (q0.c0.b, q1.c0.b, q2.c0.b)
      let m2 ←
        field.qm31_m31_sum_products3.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
          right (q0.c1.a, q1.c1.a, q2.c1.a)
      let m3 ←
        field.qm31_m31_sum_products3.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
          right (q0.c1.b, q1.c1.b, q2.c1.b)
      ok ({ c0 := { a := m, b := m1 }, c1 := { a := m2, b := m3 } } :
        RawQM31)) = ok out
    rw [run0, run1, run2, run3]
    rfl
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · change generatedM31ToExact o0 = _
        rw [exact0]
        simp [exactQm31M31Dot3, exactM31Dot3, q0, q1, q2,
          generatedQm31ToExact, generatedCm31ToExact,
          generatedM31ScalarToExactQM31, Finset.sum_range_succ]
      · change generatedM31ToExact o1 = _
        rw [exact1]
        simp [exactQm31M31Dot3, exactM31Dot3, q0, q1, q2,
          generatedQm31ToExact, generatedCm31ToExact,
          generatedM31ScalarToExactQM31, Finset.sum_range_succ]
    · apply QuadraticAlgebra.ext
      · change generatedM31ToExact o2 = _
        rw [exact2]
        simp [exactQm31M31Dot3, exactM31Dot3, q0, q1, q2,
          generatedQm31ToExact, generatedCm31ToExact,
          generatedM31ScalarToExactQM31, Finset.sum_range_succ]
      · change generatedM31ToExact o3 = _
        rw [exact3]
        simp [exactQm31M31Dot3, exactM31Dot3, q0, q1, q2,
          generatedQm31ToExact, generatedCm31ToExact,
          generatedM31ScalarToExactQM31, Finset.sum_range_succ]

#print axioms generated_qm31_m31_sum_products3_corresponds

end V7CallerCurrentReleaseR26Qm31M31SumProducts3Semantics
