import V7CallerCurrentReleaseR26TerminalLineFlush

/-!
# One complete optimized terminal-line accumulator step

This file composes scale alignment, the four-limb update, the line counter,
and the conditional three-by-four flush.  The invariant keeps only the
symbolic facts needed by the sixteen-line batch proof: canonical cells, the
four-product raw-word bound, and exact coefficient deltas.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineStep

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26TerminalLineAccumulator
open V7CallerCurrentReleaseR26TerminalLineRawLoop
open V7CallerCurrentReleaseR26TerminalLineLimbLoop
open V7CallerCurrentReleaseR26TerminalLineFlushLimb
open V7CallerCurrentReleaseR26TerminalLineFlush

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩

def scaleLimbs (scale : RawQM31) : Array Std.U32 4#usize :=
  Array.make 4#usize [scale.c0.a, scale.c0.b, scale.c1.a, scale.c1.b]

theorem scaleLimbs_canonical
    (scale : RawQM31) (canonical : GeneratedCanonicalQM31 scale) :
    CanonicalLimbs (scaleLimbs scale) := by
  intro limb limbBound
  have cases : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases canonical with ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
  rcases cases with rfl | rfl | rfl | rfl
  · change GeneratedCanonicalM31 scale.c0.a
    exact h0
  · change GeneratedCanonicalM31 scale.c0.b
    exact h1
  · change GeneratedCanonicalM31 scale.c1.a
    exact h2
  · change GeneratedCanonicalM31 scale.c1.b
    exact h3

theorem scaleLimbs_exact
    (scale : RawQM31) (limb : Nat) (limbBound : limb < 4) :
    generatedM31ToExact (limbAt (scaleLimbs scale) limb) =
      exactScaleLimb scale limb := by
  have cases : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

theorem lineFactors_exact
    (x high product : RawM31)
    (highExact : generatedM31ToExact high = exactLineFactor x 1)
    (productExact : generatedM31ToExact product = exactLineFactor x 2)
    (slot : Nat) (slotBound : slot < 3) :
    generatedM31ToExact (factorAt (lineFactors x high product) slot) =
      exactLineFactor x slot := by
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · change generatedM31ToExact x = exactLineFactor x 0
    simp [exactLineFactor]
  · change generatedM31ToExact high = exactLineFactor x 1
    exact highExact
  · change generatedM31ToExact product = exactLineFactor x 2
    exact productExact

def LineAccumulatorStateInvariant
    (processed : Nat)
    (constant : Array RawM31 4#usize)
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (sums : Array (Array RawM31 4#usize) 3#usize) : Prop :=
  CanonicalConstantLimbs constant ∧
  CanonicalLineSums sums ∧
  ∀ slot, slot < 3 → ∀ limb, limb < 4 →
    (rawCell raw slot limb).val ≤
      (processed % 4) * (2 ^ 62 - 1)

private theorem rawProduct_cast_exact
    (left right : RawM31) :
    ((rawM31Product left right : Nat) : ExactM31) =
      generatedM31ToExact left * generatedM31ToExact right := by
  simp [rawM31Product, generatedM31ToExact]

private theorem usizeWrappingSuccVal
    (count : Std.Usize) (processed : Nat)
    (countExact : count.val = processed) (processedBound : processed < 16) :
    (Std.Usize.wrapping_add count 1#usize).val = processed + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  rw [countExact]
  norm_num
  apply Nat.mod_eq_of_lt
  have small : processed + 1 < 17 := by omega
  apply lt_trans small
  rw [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num

private theorem lineLimbNoOverflow
    (processed : Nat)
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize)
    (limbs : Array Std.U32 4#usize)
    (rawBound : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
      (rawCell raw slot limb).val ≤
        (processed % 4) * (2 ^ 62 - 1))
    (factorsCanonical : CanonicalLineFactors factors)
    (limbsCanonical : CanonicalLimbs limbs) :
    ∀ slot, slot < 3 → ∀ limb, limb < 4 →
      (rawCell raw slot limb).val +
        rawM31Product (limbAt limbs limb) (factorAt factors slot) < 2 ^ 64 := by
  intro slot slotBound limb limbBound
  have rawLe := rawBound slot slotBound limb limbBound
  have productLt := canonical_m31_product_lt_two_pow_62
    (limbAt limbs limb) (factorAt factors slot)
    (limbsCanonical limb limbBound)
    (factorsCanonical slot slotBound)
  have remainderBound : processed % 4 ≤ 3 := by omega
  norm_num at rawLe productLt ⊢
  omega

theorem generated_accumulate_line_dot_corresponds
    (processed : Nat) (processedBound : processed < 16)
    (deferred : Std.U8) (scale : RawQM31) (x : RawM31)
    (count : Std.Usize)
    (constant : Array RawM31 4#usize)
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (countExact : count.val = processed)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (xCanonical : GeneratedCanonicalM31 x)
    (invariant : LineAccumulatorStateInvariant processed constant raw sums) :
    sumcheck.WeightAccumulator.impl.accumulate_line_dot
        deferred scale x deferred count constant raw sums
      ⦃ out =>
        out.1.val = processed + 1 ∧
        LineAccumulatorStateInvariant (processed + 1)
          out.2.1 out.2.2.1 out.2.2.2 ∧
        (∀ limb, limb < 4 →
          generatedM31ToExact (constantCell out.2.1 limb) =
            generatedM31ToExact (constantCell constant limb) +
              exactScaleLimb scale limb) ∧
        (∀ slot, slot < 3 → ∀ limb, limb < 4 →
          generatedM31ToExact (sumCell out.2.2.2 slot limb) +
              ((rawCell out.2.2.1 slot limb).val : ExactM31) =
            generatedM31ToExact (sumCell sums slot limb) +
              ((rawCell raw slot limb).val : ExactM31) +
              exactScaleLimb scale limb * exactLineFactor x slot) ⦄ := by
  rcases invariant with ⟨constantCanonical, sumsCanonical, rawBound⟩
  have alignmentRun := generated_line_scale_alignment_equal deferred scale
  obtain ⟨high, product, highRun, productRun, factorsCanonical,
      highExact, productExact⟩ :=
    generated_line_factors_correspond x xCanonical
  let factors := lineFactors x high product
  let limbs := scaleLimbs scale
  have factorsCanonical' : CanonicalLineFactors factors := factorsCanonical
  have limbsCanonical : CanonicalLimbs limbs :=
    scaleLimbs_canonical scale scaleCanonical
  have noOverflow := lineLimbNoOverflow processed raw factors limbs rawBound
    factorsCanonical' limbsCanonical
  have limbSpec := generated_line_limb_loop_corresponds constant raw
    factors limbs constantCanonical factorsCanonical' limbsCanonical noOverflow
  obtain ⟨limbOut, limbRun, limbPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists limbSpec
  let nextConstant := limbOut.1
  let nextRaw := limbOut.2
  have nextConstantCanonical : CanonicalConstantLimbs nextConstant :=
    limbPost.1
  have constantDelta : ∀ limb, limb < 4 →
      generatedM31ToExact (constantCell nextConstant limb) =
        generatedM31ToExact (constantCell constant limb) +
          exactScaleLimb scale limb := by
    intro limb limbBound
    have exact := limbPost.2.1 limb limbBound
    rw [if_pos limbBound] at exact
    rw [exact, scaleLimbs_exact scale limb limbBound]
  have rawDelta : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
      (rawCell nextRaw slot limb).val =
        (rawCell raw slot limb).val +
          rawM31Product (limbAt limbs limb) (factorAt factors slot) := by
    intro slot slotBound limb limbBound
    have exact := limbPost.2.2 slot slotBound limb limbBound
    simpa [show limb < 4 from limbBound] using exact
  let nextCount := Std.Usize.wrapping_add count 1#usize
  have nextCountVal : nextCount.val = processed + 1 :=
    usizeWrappingSuccVal count processed countExact processedBound
  obtain ⟨remainder, remRun, remainderVal⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Std.Usize.rem_spec nextCount (y := 4#usize) (by norm_num))
  have remainderVal' : remainder.val = (processed + 1) % 4 := by
    rw [remainderVal, nextCountVal]
    norm_num
  by_cases flush : remainder = 0#usize
  · have remainderZero : (processed + 1) % 4 = 0 := by
      have := congrArg UScalar.val flush
      simpa [remainderVal'] using this.symm
    have flushSpec := generated_line_flush_corresponds nextRaw sums
      sumsCanonical
    obtain ⟨flushOut, flushRun, flushPost⟩ :=
      Aeneas.Std.WP.spec_imp_exists flushSpec
    let finalRaw := flushOut.1
    let finalSums := flushOut.2
    have finalSumsCanonical : CanonicalLineSums finalSums := flushPost.1
    have finalRawZero : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
        (rawCell finalRaw slot limb).val = 0 := by
      intro slot slotBound limb limbBound
      have exact := flushPost.2.1 slot slotBound limb limbBound
      simpa [show slot < 3 from slotBound] using exact
    have finalSumsExact : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
        generatedM31ToExact (sumCell finalSums slot limb) =
          generatedM31ToExact (sumCell sums slot limb) +
            ((rawCell nextRaw slot limb).val : ExactM31) := by
      intro slot slotBound limb limbBound
      have exact := flushPost.2.2 slot slotBound limb limbBound
      simpa [show slot < 3 from slotBound] using exact
    have sourceRun :
        sumcheck.WeightAccumulator.impl.accumulate_line_dot
            deferred scale x deferred count constant raw sums =
          ok (nextCount, nextConstant, finalRaw, finalSums) := by
      unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot
      rw [alignmentRun]
      simp only [bind_tc_ok]
      rw [highRun]
      simp only [bind_tc_ok]
      rw [productRun]
      simp only [bind_tc_ok]
      change
        (do
          let out ←
            sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1
              { start := 0#usize, «end» := 4#usize } constant raw factors limbs
          let lineCount ← lift (Std.Usize.wrapping_add count 1#usize)
          let modulo ← lineCount % 4#usize
          if modulo = 0#usize then
            let flushed ←
              sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2
                { start := 0#usize, «end» := 3#usize } out.2 sums
            ok (lineCount, out.1, flushed.1, flushed.2)
          else ok (lineCount, out.1, out.2, sums)) = _
      rw [limbRun]
      simp only [bind_tc_ok, Std.lift]
      change
        (do
          let modulo ← nextCount % 4#usize
          if modulo = 0#usize then
            let flushed ←
              sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2
                { start := 0#usize, «end» := 3#usize } nextRaw sums
            ok (nextCount, nextConstant, flushed.1, flushed.2)
          else ok (nextCount, nextConstant, nextRaw, sums)) = _
      rw [remRun]
      simp only [bind_tc_ok]
      rw [if_pos flush, flushRun]
      rfl
    rw [sourceRun]
    simp only [Aeneas.Std.WP.spec_ok]
    refine ⟨nextCountVal, ?_, constantDelta, ?_⟩
    · refine ⟨nextConstantCanonical, finalSumsCanonical, ?_⟩
      intro slot slotBound limb limbBound
      rw [finalRawZero slot slotBound limb limbBound]
      simp
    · intro slot slotBound limb limbBound
      rw [finalRawZero slot slotBound limb limbBound]
      rw [finalSumsExact slot slotBound limb limbBound]
      rw [rawDelta slot slotBound limb limbBound]
      rw [Nat.cast_add, rawProduct_cast_exact]
      rw [scaleLimbs_exact scale limb limbBound]
      rw [lineFactors_exact x high product highExact productExact slot slotBound]
      ring
  · have remainderNonzero : (processed + 1) % 4 ≠ 0 := by
      intro zero
      apply flush
      apply UScalar.eq_of_val_eq
      simpa [remainderVal', zero]
    have remainderSucc : (processed + 1) % 4 = processed % 4 + 1 := by
      omega
    have nextRawBound : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
        (rawCell nextRaw slot limb).val ≤
          ((processed + 1) % 4) * (2 ^ 62 - 1) := by
      intro slot slotBound limb limbBound
      rw [rawDelta slot slotBound limb limbBound, remainderSucc]
      have old := rawBound slot slotBound limb limbBound
      have productLt := canonical_m31_product_lt_two_pow_62
        (limbAt limbs limb) (factorAt factors slot)
        (limbsCanonical limb limbBound)
        (factorsCanonical' slot slotBound)
      norm_num at old productLt ⊢
      omega
    have sourceRun :
        sumcheck.WeightAccumulator.impl.accumulate_line_dot
            deferred scale x deferred count constant raw sums =
          ok (nextCount, nextConstant, nextRaw, sums) := by
      unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot
      rw [alignmentRun]
      simp only [bind_tc_ok]
      rw [highRun]
      simp only [bind_tc_ok]
      rw [productRun]
      simp only [bind_tc_ok]
      change
        (do
          let out ←
            sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1
              { start := 0#usize, «end» := 4#usize } constant raw factors limbs
          let lineCount ← lift (Std.Usize.wrapping_add count 1#usize)
          let modulo ← lineCount % 4#usize
          if modulo = 0#usize then
            let flushed ←
              sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2
                { start := 0#usize, «end» := 3#usize } out.2 sums
            ok (lineCount, out.1, flushed.1, flushed.2)
          else ok (lineCount, out.1, out.2, sums)) = _
      rw [limbRun]
      simp only [bind_tc_ok, Std.lift]
      change
        (do
          let modulo ← nextCount % 4#usize
          if modulo = 0#usize then
            let flushed ←
              sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2
                { start := 0#usize, «end» := 3#usize } nextRaw sums
            ok (nextCount, nextConstant, flushed.1, flushed.2)
          else ok (nextCount, nextConstant, nextRaw, sums)) = _
      rw [remRun]
      simp only [bind_tc_ok]
      rw [if_neg flush]
    rw [sourceRun]
    simp only [Aeneas.Std.WP.spec_ok]
    refine ⟨nextCountVal, ?_, constantDelta, ?_⟩
    · exact ⟨nextConstantCanonical, sumsCanonical, nextRawBound⟩
    · intro slot slotBound limb limbBound
      rw [rawDelta slot slotBound limb limbBound]
      rw [Nat.cast_add, rawProduct_cast_exact]
      rw [scaleLimbs_exact scale limb limbBound]
      rw [lineFactors_exact x high product highExact productExact slot slotBound]
      ring

#print axioms scaleLimbs_canonical
#print axioms scaleLimbs_exact
#print axioms lineFactors_exact
#print axioms generated_accumulate_line_dot_corresponds

end V7CallerCurrentReleaseR26TerminalLineStep
