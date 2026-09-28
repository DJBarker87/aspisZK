import V7CallerCurrentReleaseR26FieldBridge
import AspisFormal.V5CuArithmeticEquivalences
import AspisFormal.V5RelationSumcheckSoundness

set_option maxHeartbeats 3000000

/-!
# Exact boundary and Horner kernels in the current R26 extraction

This file proves the two scalar kernels used by every generated relation
round.  It works on the functions inside the current production verifier
translation, not on the earlier isolated helper extraction.
-/

namespace V7CallerCurrentReleaseR26RelationEvaluatorSemantics

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26FieldBridge
open AspisV5RelationSumcheckSoundness

abbrev RawQM31 := V7CallerCurrentReleaseR26.field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

theorem qm31_add_run_corresponds
    (x y out : RawQM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y)
    (run : V7CallerCurrentReleaseR26.field.QM31.add x y = ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x + generatedQm31ToExact y := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_add_corresponds x y hx hy
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

theorem qm31_mul_run_corresponds
    (x y out : RawQM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y)
    (run : V7CallerCurrentReleaseR26.field.QM31.mul x y = ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x * generatedQm31ToExact y := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_mul_corresponds x y hx hy
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

theorem qm31_mul_m31_run_corresponds
    (x out : RawQM31) (y : V7CallerCurrentReleaseR26.field.M31)
    (hx : GeneratedCanonicalQM31 x) (hy : GeneratedCanonicalM31 y)
    (run : V7CallerCurrentReleaseR26.field.QM31.mul_m31 x y = ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = generatedQm31ToExact x *
        generatedM31ScalarToExactQM31 y := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_mul_m31_corresponds x y hx hy
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

deriving instance Inhabited for V7CallerCurrentReleaseR26.field.CM31
deriving instance Inhabited for V7CallerCurrentReleaseR26.field.QM31

def CanonicalArray (polynomial : Array RawQM31 7#usize) : Prop :=
  ∀ index, index < 7 → GeneratedCanonicalQM31 polynomial.val[index]!

def exactCoefficients (polynomial : Array RawQM31 7#usize) : Fin 7 → ExactQM31 :=
  fun index => generatedQm31ToExact polynomial.val[index.val]!

private theorem array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (inBounds : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueExact⟩ := WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using inBounds))
  have listBound : index.val < values.val.length := by
    simpa [Array.length_eq] using inBounds
  have getExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp
  simpa [valueExact, getExact] using run

private theorem usize_wrapping_sub_one_exact
    (value result : Std.Usize)
    (positive : 1 ≤ value.val)
    (resultExact : result.val = value.val - 1) :
    Std.Usize.wrapping_sub value 1#usize = result := by
  apply UScalar.eq_of_val_eq
  rw [Std.Usize.wrapping_sub_val_eq]
  have oneVal : (1#usize : Std.Usize).val = 1 := by rfl
  rw [oneVal, resultExact]
  have valueBound := value.hSize
  have rearrange :
      value.val + (UScalar.size .Usize - 1) =
        (value.val - 1) + UScalar.size .Usize := by
    omega
  rw [rearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem result_bind_congr {alpha beta : Type}
    (input : Result alpha) (left right : alpha → Result beta)
    (pointwise : ∀ value, left value = right value) :
    (do let value ← input; left value) =
      (do let value ← input; right value) := by
  cases input <;> simp [pointwise]

private theorem evaluate_loop_positive_step
    (polynomial : Array RawQM31 7#usize) (point accumulator : RawQM31)
    (degree nextDegree : Std.Usize)
    (positive : degree > 0#usize)
    (nextDegreeExact : Std.Usize.wrapping_sub degree 1#usize = nextDegree) :
    V7CallerCurrentReleaseR26.sumcheck.evaluate_loop
        polynomial point accumulator degree = (do
      let product ←
        V7CallerCurrentReleaseR26.field.QM31.mul accumulator point
      let coefficient ← Array.index_usize polynomial nextDegree
      let nextAccumulator ←
        V7CallerCurrentReleaseR26.field.QM31.add product coefficient
      V7CallerCurrentReleaseR26.sumcheck.evaluate_loop
        polynomial point nextAccumulator nextDegree) := by
  unfold V7CallerCurrentReleaseR26.sumcheck.evaluate_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [
    V7CallerCurrentReleaseR26.sumcheck.evaluate_loop.body,
    positive, if_pos, nextDegreeExact, Aeneas.Std.lift, bind_tc_ok]
  generalize multiplyRun :
      V7CallerCurrentReleaseR26.field.QM31.mul accumulator point =
        multiplyResult
  cases multiplyResult with
  | fail error => rfl
  | div => rfl
  | ok product =>
    generalize indexRun :
        Array.index_usize polynomial nextDegree = indexResult
    cases indexResult with
    | fail error => rfl
    | div => rfl
    | ok coefficient =>
      generalize addRun :
          V7CallerCurrentReleaseR26.field.QM31.add
            product coefficient = addResult
      cases addResult <;> simp [addRun]

private theorem evaluate_loop_zero
    (polynomial : Array RawQM31 7#usize) (point accumulator : RawQM31) :
    V7CallerCurrentReleaseR26.sumcheck.evaluate_loop
        polynomial point accumulator 0#usize = .ok accumulator := by
  unfold V7CallerCurrentReleaseR26.sumcheck.evaluate_loop
  rw [Aeneas.Std.loop.eq_def]
  simp [V7CallerCurrentReleaseR26.sumcheck.evaluate_loop.body]

def horner7Program
    (polynomial : Array RawQM31 7#usize) (point : RawQM31) : Result RawQM31 := do
  let coefficient6 ← Array.index_usize polynomial 6#usize
  let product5 ←
    V7CallerCurrentReleaseR26.field.QM31.mul coefficient6 point
  let coefficient5 ← Array.index_usize polynomial 5#usize
  let accumulator5 ←
    V7CallerCurrentReleaseR26.field.QM31.add product5 coefficient5
  let product4 ←
    V7CallerCurrentReleaseR26.field.QM31.mul accumulator5 point
  let coefficient4 ← Array.index_usize polynomial 4#usize
  let accumulator4 ←
    V7CallerCurrentReleaseR26.field.QM31.add product4 coefficient4
  let product3 ←
    V7CallerCurrentReleaseR26.field.QM31.mul accumulator4 point
  let coefficient3 ← Array.index_usize polynomial 3#usize
  let accumulator3 ←
    V7CallerCurrentReleaseR26.field.QM31.add product3 coefficient3
  let product2 ←
    V7CallerCurrentReleaseR26.field.QM31.mul accumulator3 point
  let coefficient2 ← Array.index_usize polynomial 2#usize
  let accumulator2 ←
    V7CallerCurrentReleaseR26.field.QM31.add product2 coefficient2
  let product1 ←
    V7CallerCurrentReleaseR26.field.QM31.mul accumulator2 point
  let coefficient1 ← Array.index_usize polynomial 1#usize
  let accumulator1 ←
    V7CallerCurrentReleaseR26.field.QM31.add product1 coefficient1
  let product0 ←
    V7CallerCurrentReleaseR26.field.QM31.mul accumulator1 point
  let coefficient0 ← Array.index_usize polynomial 0#usize
  V7CallerCurrentReleaseR26.field.QM31.add product0 coefficient0

theorem generated_evaluate_eq_horner7_program
    (polynomial : Array RawQM31 7#usize) (point : RawQM31) :
    V7CallerCurrentReleaseR26.sumcheck.evaluate polynomial point =
      horner7Program polynomial point := by
  have sub7 : Std.Usize.wrapping_sub 7#usize 1#usize = 6#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub6 : Std.Usize.wrapping_sub 6#usize 1#usize = 5#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub5 : Std.Usize.wrapping_sub 5#usize 1#usize = 4#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub4 : Std.Usize.wrapping_sub 4#usize 1#usize = 3#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub3 : Std.Usize.wrapping_sub 3#usize 1#usize = 2#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub2 : Std.Usize.wrapping_sub 2#usize 1#usize = 1#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub1 : Std.Usize.wrapping_sub 1#usize 1#usize = 0#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have gt6 : 6#usize > 0#usize := by scalar_tac
  have gt5 : 5#usize > 0#usize := by scalar_tac
  have gt4 : 4#usize > 0#usize := by scalar_tac
  have gt3 : 3#usize > 0#usize := by scalar_tac
  have gt2 : 2#usize > 0#usize := by scalar_tac
  have gt1 : 1#usize > 0#usize := by scalar_tac
  unfold V7CallerCurrentReleaseR26.sumcheck.evaluate
    V7CallerCurrentReleaseR26.sumcheck.SUMCHECK_COEFFICIENTS
  simp only [sub7, Aeneas.Std.lift, bind_tc_ok]
  unfold horner7Program
  generalize index6 : Array.index_usize polynomial 6#usize = initialResult
  cases initialResult with
  | fail error => rfl
  | div => rfl
  | ok coefficient6 =>
    simp only [bind_tc_ok]
    rw [evaluate_loop_positive_step polynomial point coefficient6
      6#usize 5#usize gt6 sub6]
    apply result_bind_congr
    intro product5
    apply result_bind_congr
    intro coefficient5
    apply result_bind_congr
    intro accumulator5
    rw [evaluate_loop_positive_step polynomial point accumulator5
      5#usize 4#usize gt5 sub5]
    apply result_bind_congr
    intro product4
    apply result_bind_congr
    intro coefficient4
    apply result_bind_congr
    intro accumulator4
    rw [evaluate_loop_positive_step polynomial point accumulator4
      4#usize 3#usize gt4 sub4]
    apply result_bind_congr
    intro product3
    apply result_bind_congr
    intro coefficient3
    apply result_bind_congr
    intro accumulator3
    rw [evaluate_loop_positive_step polynomial point accumulator3
      3#usize 2#usize gt3 sub3]
    apply result_bind_congr
    intro product2
    apply result_bind_congr
    intro coefficient2
    apply result_bind_congr
    intro accumulator2
    rw [evaluate_loop_positive_step polynomial point accumulator2
      2#usize 1#usize gt2 sub2]
    apply result_bind_congr
    intro product1
    apply result_bind_congr
    intro coefficient1
    apply result_bind_congr
    intro accumulator1
    rw [evaluate_loop_positive_step polynomial point accumulator1
      1#usize 0#usize gt1 sub1]
    apply result_bind_congr
    intro product0
    apply result_bind_congr
    intro coefficient0
    generalize lastRun :
        V7CallerCurrentReleaseR26.field.QM31.add
          product0 coefficient0 = lastResult
    cases lastResult with
    | fail error => rfl
    | div => rfl
    | ok accumulator0 =>
      simp only [bind_tc_ok]
      exact evaluate_loop_zero polynomial point accumulator0

/-- A successful generated boundary computation is exactly the maintained
arity-four boundary expression. -/
theorem generated_boundary_success_exact
    (polynomial : Array RawQM31 7#usize) (output : RawQM31)
    (canonical : CanonicalArray polynomial)
    (success :
      V7CallerCurrentReleaseR26.sumcheck.boundary_sum polynomial =
        ok output) :
    GeneratedCanonicalQM31 output ∧
      generatedQm31ToExact output =
        4 * (exactCoefficients polynomial 0 + exactCoefficients polynomial 4) := by
  have index0 := array_index_run polynomial 0#usize (by norm_num)
  have index4 := array_index_run polynomial 4#usize (by norm_num)
  unfold V7CallerCurrentReleaseR26.sumcheck.boundary_sum at success
  rw [index0, index4] at success
  simp only [bind_tc_ok] at success
  have c0 := canonical 0 (by norm_num)
  have c4 := canonical 4 (by norm_num)
  have c0Wire : GeneratedCanonicalQM31 polynomial.val[(0#usize).val]! := by
    simpa using c0
  have c4Wire : GeneratedCanonicalQM31 polynomial.val[(4#usize).val]! := by
    simpa using c4
  obtain ⟨sum, addRun, sumCanonical, sumExact⟩ :=
    generated_qm31_add_corresponds
      polynomial.val[(0#usize).val]! polynomial.val[(4#usize).val]!
      c0Wire c4Wire
  rw [addRun] at success
  simp only [bind_tc_ok] at success
  have fourCanonical :
      AspisAeneasCM31Multiplicative.CanonicalRawM31 (4#u32).val := by
    norm_num [AspisAeneasCM31Multiplicative.CanonicalRawM31]
  have outputExact := qm31_mul_m31_run_corresponds
    sum output 4#u32 sumCanonical fourCanonical success
  have fourExact :
      generatedM31ScalarToExactQM31 4#u32 = (4 : ExactQM31) := by
    rfl
  refine ⟨outputExact.1, ?_⟩
  rw [outputExact.2, sumExact, fourExact]
  simp [exactCoefficients]
  ring

private theorem result_bind_success
    {alpha beta : Type} (input : Result alpha) (next : alpha → Result beta)
    (output : beta)
    (success : (do let value ← input; next value) = ok output) :
    ∃ value, input = ok value ∧ next value = ok output := by
  cases input with
  | fail error => simp at success
  | div => simp at success
  | ok value => exact ⟨value, rfl, success⟩

/-- The twelve successful field calls made by the fixed seven-coefficient
Horner evaluator.  Keeping this execution trace separate makes the generated
control-flow inversion independent of field semantics. -/
def HornerStep
    (accumulator point coefficient next : RawQM31) : Prop :=
  ∃ product,
    V7CallerCurrentReleaseR26.field.QM31.mul
        accumulator point = ok product ∧
    V7CallerCurrentReleaseR26.field.QM31.add
        product coefficient = ok next

def Horner7Trace
    (polynomial : Array RawQM31 7#usize) (point output : RawQM31) : Prop :=
  ∃ accumulator5 accumulator4 accumulator3 accumulator2 accumulator1,
    HornerStep (polynomial.val[(6#usize).val]!) point
        (polynomial.val[(5#usize).val]!) accumulator5 ∧
    HornerStep accumulator5 point
        (polynomial.val[(4#usize).val]!) accumulator4 ∧
    HornerStep accumulator4 point
        (polynomial.val[(3#usize).val]!) accumulator3 ∧
    HornerStep accumulator3 point
        (polynomial.val[(2#usize).val]!) accumulator2 ∧
    HornerStep accumulator2 point
        (polynomial.val[(1#usize).val]!) accumulator1 ∧
    HornerStep accumulator1 point
        (polynomial.val[(0#usize).val]!) output

theorem generated_evaluate_success_yields_trace
    (polynomial : Array RawQM31 7#usize) (point output : RawQM31)
    (success :
      V7CallerCurrentReleaseR26.sumcheck.evaluate polynomial point =
        ok output) :
    Horner7Trace polynomial point output := by
  rw [generated_evaluate_eq_horner7_program] at success
  unfold horner7Program at success
  have index6 := array_index_run polynomial 6#usize (by norm_num)
  rw [index6] at success
  simp only [bind_tc_ok] at success
  obtain ⟨product5, mul5, rest5⟩ := result_bind_success _ _ _ success
  have index5 := array_index_run polynomial 5#usize (by norm_num)
  rw [index5] at rest5
  simp only [bind_tc_ok] at rest5
  obtain ⟨accumulator5, add5, rest4⟩ := result_bind_success _ _ _ rest5
  obtain ⟨product4, mul4, rest4a⟩ := result_bind_success _ _ _ rest4
  have index4 := array_index_run polynomial 4#usize (by norm_num)
  rw [index4] at rest4a
  simp only [bind_tc_ok] at rest4a
  obtain ⟨accumulator4, add4, rest3⟩ := result_bind_success _ _ _ rest4a
  obtain ⟨product3, mul3, rest3a⟩ := result_bind_success _ _ _ rest3
  have index3 := array_index_run polynomial 3#usize (by norm_num)
  rw [index3] at rest3a
  simp only [bind_tc_ok] at rest3a
  obtain ⟨accumulator3, add3, rest2⟩ := result_bind_success _ _ _ rest3a
  obtain ⟨product2, mul2, rest2a⟩ := result_bind_success _ _ _ rest2
  have index2 := array_index_run polynomial 2#usize (by norm_num)
  rw [index2] at rest2a
  simp only [bind_tc_ok] at rest2a
  obtain ⟨accumulator2, add2, rest1⟩ := result_bind_success _ _ _ rest2a
  obtain ⟨product1, mul1, rest1a⟩ := result_bind_success _ _ _ rest1
  have index1 := array_index_run polynomial 1#usize (by norm_num)
  rw [index1] at rest1a
  simp only [bind_tc_ok] at rest1a
  obtain ⟨accumulator1, add1, rest0⟩ := result_bind_success _ _ _ rest1a
  obtain ⟨product0, mul0, rest0a⟩ := result_bind_success _ _ _ rest0
  have index0 := array_index_run polynomial 0#usize (by norm_num)
  rw [index0] at rest0a
  simp only [bind_tc_ok] at rest0a
  exact ⟨accumulator5, accumulator4, accumulator3, accumulator2,
    accumulator1, ⟨product5, mul5, add5⟩, ⟨product4, mul4, add4⟩,
    ⟨product3, mul3, add3⟩, ⟨product2, mul2, add2⟩,
    ⟨product1, mul1, add1⟩, ⟨product0, mul0, rest0a⟩⟩

private theorem horner_step_run_exact
    (accumulator point coefficient product next : RawQM31)
    (accumulatorCanonical : GeneratedCanonicalQM31 accumulator)
    (pointCanonical : GeneratedCanonicalQM31 point)
    (coefficientCanonical : GeneratedCanonicalQM31 coefficient)
    (mulRun : V7CallerCurrentReleaseR26.field.QM31.mul
      accumulator point = ok product)
    (addRun : V7CallerCurrentReleaseR26.field.QM31.add
      product coefficient = ok next) :
    GeneratedCanonicalQM31 next ∧
      generatedQm31ToExact next =
        generatedQm31ToExact accumulator * generatedQm31ToExact point + generatedQm31ToExact coefficient := by
  have productExact := qm31_mul_run_corresponds
    accumulator point product accumulatorCanonical pointCanonical mulRun
  have nextExact := qm31_add_run_corresponds
    product coefficient next productExact.1 coefficientCanonical addRun
  exact ⟨nextExact.1, nextExact.2.trans (by rw [productExact.2])⟩

private theorem horner_step_exact
    (accumulator point coefficient next : RawQM31)
    (accumulatorCanonical : GeneratedCanonicalQM31 accumulator)
    (pointCanonical : GeneratedCanonicalQM31 point)
    (coefficientCanonical : GeneratedCanonicalQM31 coefficient)
    (trace : HornerStep accumulator point coefficient next) :
    GeneratedCanonicalQM31 next ∧
      generatedQm31ToExact next =
        generatedQm31ToExact accumulator * generatedQm31ToExact point + generatedQm31ToExact coefficient := by
  rcases trace with ⟨product, mulRun, addRun⟩
  exact horner_step_run_exact accumulator point coefficient product next
    accumulatorCanonical pointCanonical coefficientCanonical mulRun addRun

private theorem exact_horner_six
    {R : Type*} [CommSemiring R]
    (coefficients : Fin 7 → R) (point : R)
    (accumulator5 accumulator4 accumulator3 accumulator2 accumulator1
      output : R)
    (step5 : accumulator5 = coefficients 6 * point + coefficients 5)
    (step4 : accumulator4 = accumulator5 * point + coefficients 4)
    (step3 : accumulator3 = accumulator4 * point + coefficients 3)
    (step2 : accumulator2 = accumulator3 * point + coefficients 2)
    (step1 : accumulator1 = accumulator2 * point + coefficients 1)
    (step0 : output = accumulator1 * point + coefficients 0) :
    output =
      AspisV5CuArithmeticEquivalences.horner7Optimized point coefficients := by
  unfold AspisV5CuArithmeticEquivalences.horner7Optimized
  calc
    output = accumulator1 * point + coefficients 0 := step0
    _ = (accumulator2 * point + coefficients 1) * point + coefficients 0 :=
      congrArg (fun value => value * point + coefficients 0) step1
    _ = ((accumulator3 * point + coefficients 2) * point + coefficients 1) *
          point + coefficients 0 :=
      congrArg (fun value =>
        (value * point + coefficients 1) * point + coefficients 0) step2
    _ = (((accumulator4 * point + coefficients 3) * point + coefficients 2) *
          point + coefficients 1) * point + coefficients 0 :=
      congrArg (fun value =>
        ((value * point + coefficients 2) * point + coefficients 1) * point +
          coefficients 0) step3
    _ = ((((accumulator5 * point + coefficients 4) * point + coefficients 3) *
          point + coefficients 2) * point + coefficients 1) * point +
          coefficients 0 :=
      congrArg (fun value =>
        (((value * point + coefficients 3) * point + coefficients 2) * point +
          coefficients 1) * point + coefficients 0) step4
    _ = (((((coefficients 6 * point + coefficients 5) * point +
          coefficients 4) * point + coefficients 3) * point + coefficients 2) *
          point + coefficients 1) * point + coefficients 0 :=
      congrArg (fun value =>
        ((((value * point + coefficients 4) * point + coefficients 3) * point +
          coefficients 2) * point + coefficients 1) * point + coefficients 0)
        step5

private theorem horner_trace_exact
    (polynomial : Array RawQM31 7#usize) (point output : RawQM31)
    (canonical : CanonicalArray polynomial) (pointCanonical : GeneratedCanonicalQM31 point)
    (trace : Horner7Trace polynomial point output) :
    GeneratedCanonicalQM31 output ∧
      generatedQm31ToExact output =
        AspisV5CuArithmeticEquivalences.horner7Optimized
          (generatedQm31ToExact point) (exactCoefficients polynomial) := by
  rcases trace with ⟨accumulator5, accumulator4, accumulator3, accumulator2,
    accumulator1, step5Trace, step4Trace, step3Trace, step2Trace,
    step1Trace, step0Trace⟩
  have c6 : GeneratedCanonicalQM31 polynomial.val[(6#usize).val]! := by
    simpa using canonical 6 (by norm_num)
  have c5 : GeneratedCanonicalQM31 polynomial.val[(5#usize).val]! := by
    simpa using canonical 5 (by norm_num)
  have step5 : GeneratedCanonicalQM31 accumulator5 ∧
      generatedQm31ToExact accumulator5 =
        generatedQm31ToExact polynomial.val[(6#usize).val]! * generatedQm31ToExact point +
          generatedQm31ToExact polynomial.val[(5#usize).val]! :=
    horner_step_exact (polynomial.val[(6#usize).val]!) point
      (polynomial.val[(5#usize).val]!) accumulator5
      c6 pointCanonical c5 step5Trace
  have c4 : GeneratedCanonicalQM31 polynomial.val[(4#usize).val]! := by
    simpa using canonical 4 (by norm_num)
  have step4 : GeneratedCanonicalQM31 accumulator4 ∧
      generatedQm31ToExact accumulator4 =
        generatedQm31ToExact accumulator5 * generatedQm31ToExact point +
          generatedQm31ToExact polynomial.val[(4#usize).val]! :=
    horner_step_exact accumulator5 point
      (polynomial.val[(4#usize).val]!) accumulator4
      step5.1 pointCanonical c4 step4Trace
  have c3 : GeneratedCanonicalQM31 polynomial.val[(3#usize).val]! := by
    simpa using canonical 3 (by norm_num)
  have step3 : GeneratedCanonicalQM31 accumulator3 ∧
      generatedQm31ToExact accumulator3 =
        generatedQm31ToExact accumulator4 * generatedQm31ToExact point +
          generatedQm31ToExact polynomial.val[(3#usize).val]! :=
    horner_step_exact accumulator4 point
      (polynomial.val[(3#usize).val]!) accumulator3
      step4.1 pointCanonical c3 step3Trace
  have c2 : GeneratedCanonicalQM31 polynomial.val[(2#usize).val]! := by
    simpa using canonical 2 (by norm_num)
  have step2 : GeneratedCanonicalQM31 accumulator2 ∧
      generatedQm31ToExact accumulator2 =
        generatedQm31ToExact accumulator3 * generatedQm31ToExact point +
          generatedQm31ToExact polynomial.val[(2#usize).val]! :=
    horner_step_exact accumulator3 point
      (polynomial.val[(2#usize).val]!) accumulator2
      step3.1 pointCanonical c2 step2Trace
  have c1 : GeneratedCanonicalQM31 polynomial.val[(1#usize).val]! := by
    simpa using canonical 1 (by norm_num)
  have step1 : GeneratedCanonicalQM31 accumulator1 ∧
      generatedQm31ToExact accumulator1 =
        generatedQm31ToExact accumulator2 * generatedQm31ToExact point +
          generatedQm31ToExact polynomial.val[(1#usize).val]! :=
    horner_step_exact accumulator2 point
      (polynomial.val[(1#usize).val]!) accumulator1
      step2.1 pointCanonical c1 step1Trace
  have c0 : GeneratedCanonicalQM31 polynomial.val[(0#usize).val]! := by
    simpa using canonical 0 (by norm_num)
  have step0 : GeneratedCanonicalQM31 output ∧
      generatedQm31ToExact output =
        generatedQm31ToExact accumulator1 * generatedQm31ToExact point +
          generatedQm31ToExact polynomial.val[(0#usize).val]! :=
    horner_step_exact accumulator1 point
      (polynomial.val[(0#usize).val]!) output
      step1.1 pointCanonical c0 step0Trace
  refine ⟨step0.1, ?_⟩
  apply exact_horner_six (exactCoefficients polynomial) (generatedQm31ToExact point)
      (generatedQm31ToExact accumulator5) (generatedQm31ToExact accumulator4) (generatedQm31ToExact accumulator3)
      (generatedQm31ToExact accumulator2) (generatedQm31ToExact accumulator1) (generatedQm31ToExact output)
  · simpa [exactCoefficients] using step5.2
  · simpa [exactCoefficients] using step4.2
  · simpa [exactCoefficients] using step3.2
  · simpa [exactCoefficients] using step2.2
  · simpa [exactCoefficients] using step1.2
  · simpa [exactCoefficients] using step0.2

/-- Successful execution of the extracted six-step evaluator is Horner
evaluation in the exact field.  Canonicality is preserved at every multiply
and add, so no raw-word equality is used as a field equality by assumption. -/
theorem generated_evaluate_success_exact
    (polynomial : Array RawQM31 7#usize) (point output : RawQM31)
    (canonical : CanonicalArray polynomial) (pointCanonical : GeneratedCanonicalQM31 point)
    (success :
      V7CallerCurrentReleaseR26.sumcheck.evaluate polynomial point =
        ok output) :
    GeneratedCanonicalQM31 output ∧
      generatedQm31ToExact output =
        AspisV5CuArithmeticEquivalences.horner7Optimized
          (generatedQm31ToExact point) (exactCoefficients polynomial) := by
  exact horner_trace_exact polynomial point output canonical pointCanonical
    (generated_evaluate_success_yields_trace polynomial point output success)

/-- The same result stated as evaluation of the maintained degree-six
polynomial represented by the seven exact coefficients. -/
theorem generated_evaluate_success_relationPolynomial
    (polynomial : Array RawQM31 7#usize) (point output : RawQM31)
    (canonical : CanonicalArray polynomial) (pointCanonical : GeneratedCanonicalQM31 point)
    (success :
      V7CallerCurrentReleaseR26.sumcheck.evaluate polynomial point =
        ok output) :
    GeneratedCanonicalQM31 output ∧
      generatedQm31ToExact output =
        (relationPolynomial (exactCoefficients polynomial)).eval (generatedQm31ToExact point) := by
  have exact := generated_evaluate_success_exact polynomial point output
    canonical pointCanonical success
  refine ⟨exact.1, ?_⟩
  rw [exact.2, AspisV5CuArithmeticEquivalences.horner7_eq_poly]
  exact (eval_relationPolynomial (exactCoefficients polynomial) (generatedQm31ToExact point)).symm

#print axioms generated_evaluate_eq_horner7_program
#print axioms generated_boundary_success_exact
#print axioms generated_evaluate_success_exact
#print axioms generated_evaluate_success_relationPolynomial

end V7CallerCurrentReleaseR26RelationEvaluatorSemantics
