import V7CallerCurrentReleaseR26FieldBridge

/-!
# Exact current R26 line-batch factor loop

This file proves the inner bit loop used by `LineM31Batch`.  Starting from a
line coordinate `x`, the generated loop walks `x, 2*x^2-1, ...`; selected
index bits multiply the incoming secure-field scale by the corresponding
base-field factor.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace V7CallerCurrentReleaseR26LineBatchFactorLoop

open V7CallerCurrentReleaseR26FieldBridge

abbrev M31 := V7CallerCurrentReleaseR26.field.M31
abbrev QM31 := V7CallerCurrentReleaseR26.field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

def u32OfNatTruncate (value : Nat) : Std.U32 :=
  UScalar.ofNatCore (value % (2 ^ 32)) (by
    exact Nat.mod_lt _ (by positivity))

private theorem u32OfNatTruncate_val_eq {value : Nat}
    (bound : value < 2 ^ 32) :
    (u32OfNatTruncate value).val = value := by
  simp only [u32OfNatTruncate, UScalar.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt bound

def lineFactor : ExactM31 → Nat → ExactM31
  | x, 0 => x
  | x, n + 1 => 2 * (lineFactor x n) ^ 2 - 1

def selectedLineBit (index : Std.U32) (coordinate : Nat) : Std.U32 :=
  index &&& Std.U32.wrapping_shl 1#u32 (u32OfNatTruncate coordinate)

def lineTerm (x : M31) (index : Std.U32) (coordinate : Nat) : ExactQM31 :=
  if selectedLineBit index coordinate != 0#u32 then
    ⟨⟨lineFactor (generatedM31ToExact x) coordinate, 0⟩, 0⟩
  else 1

def linePrefix (scale : QM31) (x : M31) (index : Std.U32)
    (processed : Nat) : ExactQM31 :=
  generatedQm31ToExact scale *
    ∏ coordinate ∈ Finset.range processed, lineTerm x index coordinate

def LineFactorInvariant (scale current : QM31) (x factor : M31)
    (index : Std.U32) (bit : Nat) : Prop :=
  GeneratedCanonicalQM31 current ∧
    GeneratedCanonicalM31 factor ∧
    generatedQm31ToExact current = linePrefix scale x index bit ∧
    generatedM31ToExact factor = lineFactor (generatedM31ToExact x) bit

private theorem u32_succ_run (bit : Std.U32) (bound : bit.val < 2 ^ 32 - 1) :
    Std.U32.wrapping_add bit 1#u32 = u32OfNatTruncate (bit.val + 1) := by
  apply UScalar.eq_of_val_eq
  rw [Std.U32.wrapping_add_val_eq, u32OfNatTruncate_val_eq]
  · apply Nat.mod_eq_of_lt
    norm_num [UScalar.size_def, UScalarTy.U32_numBits_eq]
    omega
  · omega

private theorem line_factor_body_done
    (logLen index : Std.U32) (current : QM31) (factor : M31)
    (bit : Std.U32) (done : ¬ bit.val < logLen.val) :
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0.body
        logLen index current factor bit = ok (ControlFlow.done current) := by
  unfold V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0.body
  simp [UScalar.lt_equiv, done]

private theorem line_factor_body_active
    (logLen index : Std.U32) (scale current : QM31)
    (x factor : M31) (bit : Std.U32)
    (logBound : logLen.val ≤ 32)
    (active : bit.val < logLen.val)
    (invariant : LineFactorInvariant scale current x factor index bit.val) :
    ∃ nextBit nextFactor out,
      V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0.body
          logLen index current factor bit =
        ok (ControlFlow.cont (out, nextFactor, nextBit)) ∧
      nextBit.val = bit.val + 1 ∧
      LineFactorInvariant scale out x nextFactor index nextBit.val := by
  have activeScalar : bit < logLen := by
    simpa [UScalar.lt_equiv] using active
  have bitBound : bit.val < 32 := lt_of_lt_of_le active logBound
  have bitState : u32OfNatTruncate bit.val = bit := by
    apply UScalar.eq_of_val_eq
    exact u32OfNatTruncate_val_eq (lt_trans bitBound (by norm_num))
  let mask := Std.U32.wrapping_shl 1#u32 bit
  let selected := index &&& mask
  have selectedExact : selectedLineBit index bit.val = selected := by
    simp [selectedLineBit, selected, mask, bitState]
  have nextRun := u32_succ_run bit (by omega)
  let nextBit := u32OfNatTruncate (bit.val + 1)
  have nextVal : nextBit.val = bit.val + 1 :=
    u32OfNatTruncate_val_eq (by omega)
  obtain ⟨nextFactor, factorRun, factorCanonical, factorExact⟩ :=
    generated_double_x_m31_corresponds factor invariant.2.1
  by_cases selectedNonzero : selected != 0#u32
  · obtain ⟨out, outRun, outCanonical, outExact⟩ :=
      generated_qm31_mul_m31_corresponds current factor invariant.1
        invariant.2.1
    refine ⟨nextBit, nextFactor, out, ?_, nextVal, ?_⟩
    · unfold V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0.body
      rw [if_pos activeScalar]
      simp only [Std.lift, bind_tc_ok]
      change
        (if selected != 0#u32 then
            V7CallerCurrentReleaseR26.field.QM31.mul_m31 current factor >>= fun value1 =>
              V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.double_x_m31 factor >>= fun factor1 =>
                ok (ControlFlow.cont
                  (value1, factor1, Std.U32.wrapping_add bit 1#u32))
          else
            V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.double_x_m31 factor >>= fun factor1 =>
              ok (ControlFlow.cont
                (current, factor1, Std.U32.wrapping_add bit 1#u32))) = _
      rw [if_pos selectedNonzero, outRun]
      simp only [bind_tc_ok]
      rw [factorRun]
      simp only [bind_tc_ok, nextRun]
      rfl
    · refine ⟨outCanonical, factorCanonical, ?_, ?_⟩
      · rw [outExact, invariant.2.2.1]
        unfold generatedM31ScalarToExactQM31
        rw [invariant.2.2.2]
        have selectedNe : selected ≠ 0#u32 := by simpa using selectedNonzero
        have selectedVal : selected.val ≠ 0 := by
          intro zero
          apply selectedNe
          apply UScalar.eq_of_val_eq
          simpa using zero
        simp [linePrefix, Finset.prod_range_succ, lineTerm, nextVal,
          selectedExact, selectedVal]
        ring
      · rw [factorExact, invariant.2.2.2, nextVal]
        simp [lineFactor]
  · refine ⟨nextBit, nextFactor, current, ?_, nextVal, ?_⟩
    · unfold V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0.body
      rw [if_pos activeScalar]
      simp only [Std.lift, bind_tc_ok]
      change
        (if selected != 0#u32 then
            V7CallerCurrentReleaseR26.field.QM31.mul_m31 current factor >>= fun value1 =>
              V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.double_x_m31 factor >>= fun factor1 =>
                ok (ControlFlow.cont
                  (value1, factor1, Std.U32.wrapping_add bit 1#u32))
          else
            V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.double_x_m31 factor >>= fun factor1 =>
              ok (ControlFlow.cont
                (current, factor1, Std.U32.wrapping_add bit 1#u32))) = _
      rw [if_neg selectedNonzero, factorRun]
      simp only [bind_tc_ok, nextRun]
      rfl
    · refine ⟨invariant.1, factorCanonical, ?_, ?_⟩
      · rw [invariant.2.2.1]
        have selectedVal : selected.val = 0 := by simpa using selectedNonzero
        simp [linePrefix, Finset.prod_range_succ, lineTerm, nextVal,
          selectedExact, selectedVal]
      · rw [factorExact, invariant.2.2.2, nextVal]
        simp [lineFactor]

/-- Exact semantics of one generated line-factor bit loop. -/
theorem generated_line_factor_loop_corresponds
    (logLen index : Std.U32) (scale : QM31) (x : M31)
    (logBound : logLen.val ≤ 32)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (xCanonical : GeneratedCanonicalM31 x) :
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0
        logLen index scale x 0#u32
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out = linePrefix scale x index logLen.val ⦄ := by
  simp only [V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : QM31 × M31 × Std.U32 => logLen.val - state.2.2.val)
    (fun state => state.2.2.val ≤ logLen.val ∧
      LineFactorInvariant scale state.1 x state.2.1 index state.2.2.val)
    (fun out => GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = linePrefix scale x index logLen.val)
  · rintro ⟨current, factor, bit⟩ ⟨bitLe, stateInvariant⟩
    dsimp only at bitLe stateInvariant ⊢
    by_cases active : bit.val < logLen.val
    · obtain ⟨nextBit, nextFactor, out, bodyRun, nextVal, nextInvariant⟩ :=
        line_factor_body_active logLen index scale current x factor bit
          logBound active stateInvariant
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [nextVal]
        omega
      · simpa [nextVal] using nextInvariant
      · rw [nextVal]
        omega
    · have atEnd : bit.val = logLen.val := by omega
      rw [line_factor_body_done logLen index current factor bit active]
      simp only [Aeneas.Std.WP.spec_ok]
      exact ⟨stateInvariant.1, by simpa [atEnd] using stateInvariant.2.2.1⟩
  · refine ⟨by norm_num, scaleCanonical, xCanonical, ?_, ?_⟩
    · simp [linePrefix]
    · simp [generatedM31ToExact, lineFactor]

#print axioms generated_line_factor_loop_corresponds

end V7CallerCurrentReleaseR26LineBatchFactorLoop
