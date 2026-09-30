import V7CallerCurrentReleaseR30CircleArithmeticCanonical
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Canonical secure-circle outputs for the current production caller

This module follows the current generated source of the inverse, secure-circle
map, sampler, and circle-factor loop.  It establishes only canonicality, which
is the remaining premise needed by the already checked terminal theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30SecureCircleCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30CircleArithmeticCanonical

abbrev RawM31 := field.M31
abbrev RawCM31 := field.CM31
abbrev RawQM31 := field.QM31

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private def squareBody
    (state : core.ops.range.Range Std.Usize × RawM31) :
    Result (ControlFlow (core.ops.range.Range Std.Usize × RawM31) RawM31) :=
  field.square_n_loop.body state.1 state.2

private theorem square_body_cont_canonical
    (state next : core.ops.range.Range Std.Usize × RawM31)
    (edge : squareBody state = ok (cont next))
    (canonical : GeneratedCanonicalM31 state.2) :
    GeneratedCanonicalM31 next.2 := by
  rcases state with ⟨iter, value⟩
  rcases next with ⟨iterNext, valueNext⟩
  change GeneratedCanonicalM31 value at canonical
  change GeneratedCanonicalM31 valueNext
  unfold squareBody at edge
  unfold field.square_n_loop.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterOut⟩
  cases option with
  | none =>
      simp only at edge
      cases edge
  | some index =>
      rw [bind_eq_ok_iff] at edge
      obtain ⟨squared, squaredRun, edge⟩ := edge
      have exact : valueNext = squared := by
        exact (congrArg Prod.snd
          (ControlFlow.cont.inj (Result.ok.inj edge))).symm
      rw [exact]
      obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
        generated_m31_mul_corresponds value value canonical canonical
      have outputExact : squared = expected :=
        Result.ok.inj (squaredRun.symm.trans expectedRun)
      rw [outputExact]
      exact expectedCanonical

private theorem square_trace_canonical
    {state : core.ops.range.Range Std.Usize × RawM31} {output : RawM31}
    (trace : ExactLoopTrace squareBody state output)
    (canonical : GeneratedCanonicalM31 state.2) :
    GeneratedCanonicalM31 output := by
  induction trace with
  | @done state output edge =>
      rcases state with ⟨iter, value⟩
      change GeneratedCanonicalM31 value at canonical
      unfold squareBody at edge
      unfold field.square_n_loop.body at edge
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
      rcases iteratorPair with ⟨option, iterOut⟩
      cases option with
      | none =>
          simp at edge
          cases edge
          exact canonical
      | some index =>
          rw [bind_eq_ok_iff] at edge
          obtain ⟨squared, squaredRun, edge⟩ := edge
          cases edge
  | cont edge tail inductionHypothesis =>
      exact inductionHypothesis
        (square_body_cont_canonical _ _ edge canonical)

theorem successful_square_n_canonical
    (value output : RawM31) (count : Std.Usize)
    (canonical : GeneratedCanonicalM31 value)
    (run : field.square_n value count = ok output) :
    GeneratedCanonicalM31 output := by
  unfold field.square_n at run
  unfold field.square_n_loop at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace squareBody
    ({ start := 0#usize, «end» := count }, value) output run
  exact square_trace_canonical trace canonical

private theorem successful_m31_mul_canonical
    (left right output : RawM31)
    (leftCanonical : GeneratedCanonicalM31 left)
    (rightCanonical : GeneratedCanonicalM31 right)
    (run : field.M31.mul left right = ok output) :
    GeneratedCanonicalM31 output := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_m31_mul_corresponds left right leftCanonical rightCanonical
  have exact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

private theorem successful_m31_add_canonical
    (left right output : RawM31)
    (leftCanonical : GeneratedCanonicalM31 left)
    (rightCanonical : GeneratedCanonicalM31 right)
    (run : field.M31.add left right = ok output) :
    GeneratedCanonicalM31 output := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_m31_add_corresponds left right leftCanonical rightCanonical
  have exact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

theorem successful_m31_inv_canonical
    (value output : RawM31)
    (canonical : GeneratedCanonicalM31 value)
    (run : field.M31.inv value = ok output) :
    GeneratedCanonicalM31 output := by
  unfold field.M31.inv at run
  simp only [massert] at run
  split at run
  · simp only [bind_tc_ok] at run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m, mRun, run⟩ := run
    have mCanonical := successful_m31_mul_canonical value value m
      canonical canonical mRun
    rw [bind_eq_ok_iff] at run
    obtain ⟨t2, t2Run, run⟩ := run
    have t2Canonical := successful_m31_mul_canonical m value t2
      mCanonical canonical t2Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m1, m1Run, run⟩ := run
    have m1Canonical := successful_square_n_canonical t2 m1 2#usize
      t2Canonical m1Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨t4, t4Run, run⟩ := run
    have t4Canonical := successful_m31_mul_canonical m1 t2 t4
      m1Canonical t2Canonical t4Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m2, m2Run, run⟩ := run
    have m2Canonical := successful_square_n_canonical t4 m2 4#usize
      t4Canonical m2Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨t8, t8Run, run⟩ := run
    have t8Canonical := successful_m31_mul_canonical m2 t4 t8
      m2Canonical t4Canonical t8Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m3, m3Run, run⟩ := run
    have m3Canonical := successful_square_n_canonical t8 m3 8#usize
      t8Canonical m3Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨t16, t16Run, run⟩ := run
    have t16Canonical := successful_m31_mul_canonical m3 t8 t16
      m3Canonical t8Canonical t16Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m4, m4Run, run⟩ := run
    have m4Canonical := successful_square_n_canonical t16 m4 8#usize
      t16Canonical m4Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨t24, t24Run, run⟩ := run
    have t24Canonical := successful_m31_mul_canonical m4 t8 t24
      m4Canonical t8Canonical t24Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m5, m5Run, run⟩ := run
    have m5Canonical := successful_square_n_canonical t24 m5 4#usize
      t24Canonical m5Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨t28, t28Run, run⟩ := run
    have t28Canonical := successful_m31_mul_canonical m5 t4 t28
      m5Canonical t4Canonical t28Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m6, m6Run, run⟩ := run
    have m6Canonical := successful_m31_mul_canonical t28 t28 m6
      t28Canonical t28Canonical m6Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨t29, t29Run, run⟩ := run
    have t29Canonical := successful_m31_mul_canonical m6 value t29
      m6Canonical canonical t29Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨t30, t30Run, run⟩ := run
    have t30Canonical := successful_m31_mul_canonical t29 t29 t30
      t29Canonical t29Canonical t30Run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m7, m7Run, run⟩ := run
    have m7Canonical := successful_m31_mul_canonical t30 t30 m7
      t30Canonical t30Canonical m7Run
    exact successful_m31_mul_canonical m7 value output m7Canonical canonical run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨ignored, impossible, _⟩ := run
    cases impossible

theorem successful_m31_neg_canonical
    (value output : RawM31)
    (canonical : GeneratedCanonicalM31 value)
    (run : field.M31.neg value = ok output) :
    GeneratedCanonicalM31 output := by
  unfold field.M31.neg at run
  split at run
  · simp only [Result.ok.injEq] at run
    subst output
    unfold GeneratedCanonicalM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31
    norm_num
  · simp only [Aeneas.Std.lift, bind_tc_ok] at run
    rename_i valueNonzeroRaw
    have outputExact : output = field.P.wrapping_sub value :=
      (Result.ok.inj run).symm
    rw [outputExact]
    unfold GeneratedCanonicalM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at canonical ⊢
    rw [Std.U32.wrapping_sub_val_eq,
      AspisAeneasCM31Multiplicative.u32_size_eq]
    have pValue : field.P.val = 2147483647 := by simp [field.P]
    rw [pValue]
    simp only [AspisAeneasCM31Multiplicative.u32Cardinality,
      AspisAeneasCM31Multiplicative.m31Modulus] at canonical ⊢
    change (2147483647 + (2 ^ 32 - value.val)) % 2 ^ 32 < 2147483647
    change value.val < 2147483647 at canonical
    have rewritten : 2147483647 + (2 ^ 32 - value.val) =
        (2147483647 - value.val) + 2 ^ 32 := by
      omega
    rw [rewritten, Nat.add_mod_right]
    have reducedBound : 2147483647 - value.val < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt reducedBound]
    have valueNonzero : value.val ≠ 0 := by
      intro valueZero
      apply valueNonzeroRaw
      apply UScalar.eq_of_val_eq
      simpa using valueZero
    omega

theorem successful_cm31_inv_canonical
    (value output : RawCM31)
    (canonical : GeneratedCanonicalCM31 value)
    (run : field.CM31.inv value = ok output) :
    GeneratedCanonicalCM31 output := by
  unfold field.CM31.inv field.CM31.inv_with at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨squareA, squareARun, run⟩ := run
  have squareACanonical := successful_m31_mul_canonical value.a value.a squareA
    canonical.1 canonical.1 squareARun
  rw [bind_eq_ok_iff] at run
  obtain ⟨squareB, squareBRun, run⟩ := run
  have squareBCanonical := successful_m31_mul_canonical value.b value.b squareB
    canonical.2 canonical.2 squareBRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨norm, normRun, run⟩ := run
  have normCanonical := successful_m31_add_canonical squareA squareB norm
    squareACanonical squareBCanonical normRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨inverseNorm, inverseNormRun, run⟩ := run
  have inverseNormCanonical := successful_m31_inv_canonical norm inverseNorm
    normCanonical inverseNormRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨outA, outARun, run⟩ := run
  have outACanonical := successful_m31_mul_canonical value.a inverseNorm outA
    canonical.1 inverseNormCanonical outARun
  rw [bind_eq_ok_iff] at run
  obtain ⟨negativeB, negativeBRun, run⟩ := run
  have negativeBCanonical := successful_m31_neg_canonical value.b negativeB
    canonical.2 negativeBRun
  rw [bind_eq_ok_iff] at run
  obtain ⟨outB, outBRun, run⟩ := run
  have outBCanonical := successful_m31_mul_canonical negativeB inverseNorm outB
    negativeBCanonical inverseNormCanonical outBRun
  simp only [Result.ok.injEq] at run
  subst output
  exact ⟨outACanonical, outBCanonical⟩

private theorem successful_cm31_sub_canonical
    (left right output : RawCM31)
    (leftCanonical : GeneratedCanonicalCM31 left)
    (rightCanonical : GeneratedCanonicalCM31 right)
    (run : field.CM31.sub left right = ok output) :
    GeneratedCanonicalCM31 output := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_cm31_sub_corresponds left right leftCanonical rightCanonical
  have exact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

private theorem successful_cm31_mul_canonical
    (left right output : RawCM31)
    (leftCanonical : GeneratedCanonicalCM31 left)
    (rightCanonical : GeneratedCanonicalCM31 right)
    (run : field.CM31.mul left right = ok output) :
    GeneratedCanonicalCM31 output := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_cm31_mul_corresponds left right leftCanonical rightCanonical
  have exact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

private theorem successful_mul_by_r_canonical
    (value output : RawCM31)
    (canonical : GeneratedCanonicalCM31 value)
    (run : field.mul_by_r value = ok output) :
    GeneratedCanonicalCM31 output := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_mul_by_r_corresponds value canonical
  have exact : output = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

private theorem successful_cm31_neg_canonical
    (value output : RawCM31)
    (canonical : GeneratedCanonicalCM31 value)
    (run : field.CM31.neg value = ok output) :
    GeneratedCanonicalCM31 output := by
  unfold field.CM31.neg at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨outA, outARun, run⟩ := run
  have outACanonical := successful_m31_neg_canonical value.a outA
    canonical.1 outARun
  rw [bind_eq_ok_iff] at run
  obtain ⟨outB, outBRun, run⟩ := run
  have outBCanonical := successful_m31_neg_canonical value.b outB
    canonical.2 outBRun
  simp only [Result.ok.injEq] at run
  subst output
  exact ⟨outACanonical, outBCanonical⟩

theorem successful_qm31_try_inv_some_canonical
    (value output : RawQM31)
    (canonical : GeneratedCanonicalQM31 value)
    (run : field.QM31.try_inv value = ok (some output)) :
    GeneratedCanonicalQM31 output := by
  unfold field.QM31.try_inv at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨isZero, isZeroRun, run⟩ := run
  cases isZero with
  | true =>
      simp at run
  | false =>
      simp only [Bool.false_eq_true, if_false] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨square0, square0Run, run⟩ := run
      obtain ⟨expected0, expected0Run, square0Canonical, _⟩ :=
        generated_cm31_square_canonical value.c0 canonical.1
      have square0Exact : square0 = expected0 :=
        Result.ok.inj (square0Run.symm.trans expected0Run)
      rw [square0Exact] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨square1, square1Run, run⟩ := run
      obtain ⟨expected1, expected1Run, square1Canonical, _⟩ :=
        generated_cm31_square_canonical value.c1 canonical.2
      have square1Exact : square1 = expected1 :=
        Result.ok.inj (square1Run.symm.trans expected1Run)
      rw [square1Exact] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨rTimesSquare1, rTimesSquare1Run, run⟩ := run
      have rTimesSquare1Canonical := successful_mul_by_r_canonical expected1
        rTimesSquare1 square1Canonical rTimesSquare1Run
      rw [bind_eq_ok_iff] at run
      obtain ⟨norm, normRun, run⟩ := run
      have normCanonical := successful_cm31_sub_canonical expected0 rTimesSquare1 norm
        square0Canonical rTimesSquare1Canonical normRun
      rw [bind_eq_ok_iff] at run
      obtain ⟨inverseNorm, inverseNormRun, run⟩ := run
      have inverseNormCanonical := successful_cm31_inv_canonical norm inverseNorm
        normCanonical inverseNormRun
      rw [bind_eq_ok_iff] at run
      obtain ⟨out0, out0Run, run⟩ := run
      have out0Canonical := successful_cm31_mul_canonical value.c0 inverseNorm out0
        canonical.1 inverseNormCanonical out0Run
      rw [bind_eq_ok_iff] at run
      obtain ⟨negative1, negative1Run, run⟩ := run
      have negative1Canonical := successful_cm31_neg_canonical value.c1 negative1
        canonical.2 negative1Run
      rw [bind_eq_ok_iff] at run
      obtain ⟨out1, out1Run, run⟩ := run
      have out1Canonical := successful_cm31_mul_canonical negative1 inverseNorm out1
        negative1Canonical inverseNormCanonical out1Run
      simp only [Result.ok.injEq, Option.some.injEq] at run
      subst output
      exact ⟨out0Canonical, out1Canonical⟩

private theorem qm31_one_canonical :
    GeneratedCanonicalQM31 field.QM31.ONE := by
  unfold GeneratedCanonicalQM31 GeneratedCanonicalCM31
  simp only [field.QM31.ONE]
  repeat' constructor <;>
    norm_num [AspisAeneasCM31Multiplicative.CanonicalRawM31]

theorem successful_secure_circle_point_canonical
    (parameter : RawQM31) (point : circle.SecureCirclePoint)
    (parameterCanonical : GeneratedCanonicalQM31 parameter)
    (run : circle.secure_circle_point_from_parameter parameter = ok (.Ok point)) :
    GeneratedCanonicalQM31 point.x ∧ GeneratedCanonicalQM31 point.y := by
  unfold circle.secure_circle_point_from_parameter at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨square, squareRun, run⟩ := run
  obtain ⟨expectedSquare, expectedSquareRun, squareCanonical, _⟩ :=
    generated_qm31_square_corresponds parameter parameterCanonical
  have squareExact : square = expectedSquare :=
    Result.ok.inj (squareRun.symm.trans expectedSquareRun)
  rw [squareExact] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨q, qRun, run⟩ := run
  obtain ⟨expectedQ, expectedQRun, qCanonical, _⟩ :=
    generated_qm31_add_corresponds field.QM31.ONE expectedSquare
      qm31_one_canonical squareCanonical
  have qExact : q = expectedQ :=
    Result.ok.inj (qRun.symm.trans expectedQRun)
  rw [qExact] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨inverseOption, inverseOptionRun, run⟩ := run
  cases inverseOption with
  | none =>
      simp only [core.option.Option.ok_or, bind_tc_ok] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨flow, flowRun, run⟩ := run
      cases flow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
      | Continue value =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
  | some inverse =>
      have inverseCanonical := successful_qm31_try_inv_some_canonical expectedQ inverse
        qCanonical inverseOptionRun
      simp only [core.option.Option.ok_or, bind_tc_ok] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨flow, flowRun, run⟩ := run
      have flowExact : flow = core.ops.control_flow.ControlFlow.Continue inverse := by
        have branchExact :
            ok (core.ops.control_flow.ControlFlow.Continue inverse) = ok flow := by
          simpa [core.result.Result.Insts.CoreOpsTry.branch] using flowRun
        exact (Result.ok.inj branchExact).symm
      rw [flowExact] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨q1, q1Run, run⟩ := run
      obtain ⟨expectedQ1, expectedQ1Run, q1Canonical, _⟩ :=
        generated_qm31_sub_corresponds field.QM31.ONE expectedSquare
          qm31_one_canonical squareCanonical
      have q1Exact : q1 = expectedQ1 :=
        Result.ok.inj (q1Run.symm.trans expectedQ1Run)
      rw [q1Exact] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨x, xRun, run⟩ := run
      have xCanonical : GeneratedCanonicalQM31 x := by
        obtain ⟨expectedX, expectedXRun, expectedXCanonical, _⟩ :=
          generated_qm31_mul_corresponds expectedQ1 inverse q1Canonical
            inverseCanonical
        have xExact : x = expectedX :=
          Result.ok.inj (xRun.symm.trans expectedXRun)
        rw [xExact]
        exact expectedXCanonical
      rw [bind_eq_ok_iff] at run
      obtain ⟨twiceParameter, twiceParameterRun, run⟩ := run
      obtain ⟨expectedTwice, expectedTwiceRun, twiceCanonical, _⟩ :=
        generated_qm31_add_corresponds parameter parameter parameterCanonical
          parameterCanonical
      have twiceExact : twiceParameter = expectedTwice :=
        Result.ok.inj (twiceParameterRun.symm.trans expectedTwiceRun)
      rw [twiceExact] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨y, yRun, run⟩ := run
      have yCanonical : GeneratedCanonicalQM31 y := by
        obtain ⟨expectedY, expectedYRun, expectedYCanonical, _⟩ :=
          generated_qm31_mul_corresponds expectedTwice inverse twiceCanonical
            inverseCanonical
        have yExact : y = expectedY :=
          Result.ok.inj (yRun.symm.trans expectedYRun)
        rw [yExact]
        exact expectedYCanonical
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at run
      subst point
      exact ⟨xCanonical, yCanonical⟩

theorem successful_secure_ood_circle_point_canonical
    (parameter : RawQM31) (point : circle.SecureCirclePoint)
    (parameterCanonical : GeneratedCanonicalQM31 parameter)
    (run : circle.secure_ood_circle_point_from_parameter parameter = ok (.Ok point)) :
    GeneratedCanonicalQM31 point.x ∧ GeneratedCanonicalQM31 point.y := by
  unfold circle.secure_ood_circle_point_from_parameter at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨initial, initialRun, run⟩ := run
  cases initial with
  | Err error =>
      rw [bind_eq_ok_iff] at run
      obtain ⟨flow, flowRun, run⟩ := run
      cases flow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
      | Continue value =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
  | Ok initialPoint =>
      have initialCanonical := successful_secure_circle_point_canonical parameter
        initialPoint parameterCanonical initialRun
      rw [bind_eq_ok_iff] at run
      obtain ⟨flow, flowRun, run⟩ := run
      have flowExact : flow = core.ops.control_flow.ControlFlow.Continue initialPoint := by
        have branchExact :
            ok (core.ops.control_flow.ControlFlow.Continue initialPoint) = ok flow := by
          simpa [core.result.Result.Insts.CoreOpsTry.branch] using flowRun
        exact (Result.ok.inj branchExact).symm
      rw [flowExact] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨inSubfield, inSubfieldRun, run⟩ := run
      cases inSubfield with
      | true => simp at run
      | false =>
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq,
            core.result.Result.Ok.injEq] at run
          subst point
          exact initialCanonical

abbrev Transcript := transcript.Transcript
abbrev CircleSamplerState := core.ops.range.Range Std.U32 × Transcript
abbrev CircleSamplerOutput :=
  (core.result.Result circle.SecureCirclePoint transcript.CirclePointSampleError) ×
    Transcript

private def circleSamplerBody (state : CircleSamplerState) :
    Result (ControlFlow CircleSamplerState CircleSamplerOutput) :=
  transcript.Transcript.impl.challenge_secure_circle_point_loop.body state.1 state.2

private theorem circle_sampler_done_canonical
    (state : CircleSamplerState) (output : CircleSamplerOutput)
    (point : circle.SecureCirclePoint)
    (edge : circleSamplerBody state = ok (done output))
    (outputExact : output.1 = .Ok point) :
    GeneratedCanonicalQM31 point.x ∧ GeneratedCanonicalQM31 point.y := by
  rcases state with ⟨iter, self⟩
  unfold circleSamplerBody at edge
  unfold transcript.Transcript.impl.challenge_secure_circle_point_loop.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterNext⟩
  cases option with
  | none =>
      simp at edge
      rw [← edge] at outputExact
      simp at outputExact
  | some index =>
      rw [bind_eq_ok_iff] at edge
      obtain ⟨challengePair, challengeRun, edge⟩ := edge
      rcases challengePair with ⟨challenge, selfAfterChallenge⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨mapped, mappedRun, edge⟩ := edge
      cases challenge with
      | Err error =>
          simp [core.result.Result.map_err,
            transcript.Transcript.challenge_secure_circle_point.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedCirclePointSampleError.call_once]
            at mappedRun
          subst mapped
          rw [bind_eq_ok_iff] at edge
          obtain ⟨flow, flowRun, edge⟩ := edge
          cases flow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at edge
                  rw [← edge] at outputExact
                  simp at outputExact
          | Continue value =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
      | Ok parameter =>
          have parameterCanonical :=
            V7CallerCurrentReleaseR30ChallengeCanonical.successful_challenge_qm31_canonical self
            selfAfterChallenge parameter challengeRun
          simp [core.result.Result.map_err] at mappedRun
          subst mapped
          rw [bind_eq_ok_iff] at edge
          obtain ⟨flow, flowRun, edge⟩ := edge
          have flowExact : flow = core.ops.control_flow.ControlFlow.Continue parameter := by
            have branchExact :
                ok (core.ops.control_flow.ControlFlow.Continue parameter) = ok flow := by
              simpa [core.result.Result.Insts.CoreOpsTry.branch] using flowRun
            exact (Result.ok.inj branchExact).symm
          rw [flowExact] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨inSubfield, inSubfieldRun, edge⟩ := edge
          cases inSubfield with
          | true =>
              simp at edge
          | false =>
              simp only [Bool.false_eq_true, if_false] at edge
              rw [bind_eq_ok_iff] at edge
              obtain ⟨circleResult, circleRun, edge⟩ := edge
              cases circleResult with
              | Err error =>
                  simp only at edge
                  cases edge
              | Ok sampledPoint =>
                  have sampledCanonical :=
                    successful_secure_ood_circle_point_canonical parameter sampledPoint
                      parameterCanonical circleRun
                  simp only at edge
                  have doneExact := ControlFlow.done.inj (Result.ok.inj edge)
                  rw [← doneExact] at outputExact
                  cases outputExact
                  exact sampledCanonical

private theorem circle_sampler_trace_canonical
    {state : CircleSamplerState} {output : CircleSamplerOutput}
    (point : circle.SecureCirclePoint)
    (trace : ExactLoopTrace circleSamplerBody state output)
    (outputExact : output.1 = .Ok point) :
    GeneratedCanonicalQM31 point.x ∧ GeneratedCanonicalQM31 point.y := by
  induction trace with
  | @done state output edge =>
      exact circle_sampler_done_canonical state output point edge outputExact
  | cont edge tail inductionHypothesis =>
      exact inductionHypothesis outputExact

theorem successful_challenge_secure_circle_point_canonical
    (self selfOut : Transcript) (point : circle.SecureCirclePoint)
    (run : transcript.Transcript.impl.challenge_secure_circle_point self =
      ok (.Ok point, selfOut)) :
    GeneratedCanonicalQM31 point.x ∧ GeneratedCanonicalQM31 point.y := by
  unfold transcript.Transcript.impl.challenge_secure_circle_point at run
  unfold transcript.Transcript.impl.challenge_secure_circle_point_loop at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace circleSamplerBody
    ({ start := 0#u32, «end» := transcript.CIRCLE_POINT_RETRY_LIMIT }, self)
    (.Ok point, selfOut) run
  exact circle_sampler_trace_canonical point trace rfl

#print axioms successful_square_n_canonical
#print axioms successful_m31_inv_canonical
#print axioms successful_m31_neg_canonical
#print axioms successful_cm31_inv_canonical
#print axioms successful_qm31_try_inv_some_canonical
#print axioms successful_secure_circle_point_canonical
#print axioms successful_secure_ood_circle_point_canonical
#print axioms successful_challenge_secure_circle_point_canonical

end V7CallerCurrentReleaseR30SecureCircleCanonical
