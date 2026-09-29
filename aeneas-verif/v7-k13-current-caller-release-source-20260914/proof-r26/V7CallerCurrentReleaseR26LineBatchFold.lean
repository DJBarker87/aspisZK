import V7CallerCurrentReleaseR26LineBatchFoldLoop

/-!
# Exact public current line-batch fold

This file lifts the verified 16-entry mutation loop through the public helper
and records the exact two-unit deferred-halving increment.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26LineBatchFold

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFoldStep
open V7CallerCurrentReleaseR26LineBatchFoldLoop

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

private theorem wrappingAddTwoExact
    (value : Std.U8) (bound : value.val ≤ 253) :
    (Std.U8.wrapping_add value 2#u8).val = value.val + 2 := by
  rw [Std.U8.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  norm_num [UScalar.size, U8.size, U8.numBits, UScalarTy.U8_numBits_eq]
  omega

/-- A successful public fold updates all sixteen line entries by the exact
arity-four numerator and increments the deferred-halving counter by two. -/
theorem fold_line_m31_batch_arity4_exact
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Std.U8) (alpha alpha2 alpha3 : RawQM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (deferredOut : Std.U8)
    (lengthExact : scales.val.length = 16)
    (sameLength : xs.val.length = scales.val.length)
    (deferredBound : deferred.val ≤ 253)
    (hscales : CanonicalQM31Slice scales)
    (hxs : CanonicalM31Slice xs)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run :
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
        scales xs deferred alpha alpha2 alpha3 =
          ok (scalesOut, xsOut, deferredOut)) :
    FoldPrefix (generatedQm31ToExact alpha) scales xs
        (scalesOut, xsOut, 16#usize) ∧
      deferredOut.val = deferred.val + 2 := by
  unfold sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4 at run
  cases loopEquation :
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop
        scales xs alpha alpha2 alpha3 0#usize with
  | fail error => simp [loopEquation] at run
  | div => simp [loopEquation] at run
  | ok output =>
      rcases output with ⟨loopScales, loopXs⟩
      simp only [loopEquation, bind_tc_ok, Std.lift] at run
      have outputs :
          (loopScales, loopXs, Std.U8.wrapping_add deferred 2#u8) =
            (scalesOut, xsOut, deferredOut) := Result.ok.inj run
      have scalesExact : loopScales = scalesOut :=
        congrArg Prod.fst outputs
      have xsExact : loopXs = xsOut :=
        congrArg (fun value => value.2.1) outputs
      have deferredExact : Std.U8.wrapping_add deferred 2#u8 = deferredOut :=
        congrArg (fun value => value.2.2) outputs
      subst scalesOut
      subst xsOut
      subst deferredOut
      have linePrefix := fold_line_m31_batch_loop_exact scales xs loopScales
        loopXs alpha alpha2 alpha3 lengthExact sameLength hscales hxs halpha
        halpha2 halpha3 halpha2Exact halpha3Exact loopEquation
      exact ⟨linePrefix, wrappingAddTwoExact deferred deferredBound⟩

/-- The completed public fold exposes the exact natural-number entry facts
without requiring a downstream projection from `FoldPrefix`. -/
theorem fold_line_m31_batch_arity4_processed
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Std.U8) (alpha alpha2 alpha3 : RawQM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (deferredOut : Std.U8)
    (lengthExact : scales.val.length = 16)
    (sameLength : xs.val.length = scales.val.length)
    (hscales : CanonicalQM31Slice scales)
    (hxs : CanonicalM31Slice xs)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run :
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
        scales xs deferred alpha alpha2 alpha3 =
          ok (scalesOut, xsOut, deferredOut)) :
    ∀ position : Fin 16,
      LineEntryExact (generatedQm31ToExact alpha)
        scales xs scalesOut xsOut position.val := by
  unfold sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4 at run
  cases loopEquation :
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop
        scales xs alpha alpha2 alpha3 0#usize with
  | fail error => simp [loopEquation] at run
  | div => simp [loopEquation] at run
  | ok output =>
      rcases output with ⟨loopScales, loopXs⟩
      simp only [loopEquation, bind_tc_ok, Std.lift] at run
      have outputs :
          (loopScales, loopXs, Std.U8.wrapping_add deferred 2#u8) =
            (scalesOut, xsOut, deferredOut) := Result.ok.inj run
      have scalesExact : loopScales = scalesOut :=
        congrArg Prod.fst outputs
      have xsExact : loopXs = xsOut :=
        congrArg (fun value => value.2.1) outputs
      subst scalesOut
      subst xsOut
      exact fold_line_m31_batch_loop_processed scales xs loopScales loopXs
        alpha alpha2 alpha3 lengthExact sameLength hscales hxs halpha halpha2
        halpha3 halpha2Exact halpha3Exact loopEquation

#print axioms fold_line_m31_batch_arity4_exact
#print axioms fold_line_m31_batch_arity4_processed

end V7CallerCurrentReleaseR26LineBatchFold
