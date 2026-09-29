import V7CallerCurrentReleaseR26TerminalGroupedComponent
import V7CallerCurrentReleaseR26HalfBridge

/-!
# Exact deferred halving used by the terminal line accumulator

The optimized terminal path postpones line divisions and applies them once to
the accumulated QM31 result.  This theorem gives the generated loop its exact
field meaning for an arbitrary `u8` count.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineHalving

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26HalfBridge

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

private theorem wrappingSuccExact
    (index count : Std.U8) (active : index < count) :
    (Std.U8.wrapping_add index 1#u8).val = index.val + 1 := by
  rw [Std.U8.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  have countBound := count.hBounds
  rw [UScalar.lt_equiv] at active
  norm_num [UScalar.size, U8.size, U8.numBits,
    UScalarTy.U8_numBits_eq] at countBound ⊢
  omega

private theorem halveBodyActive
    (initial current next : RawQM31) (count index : Std.U8)
    (active : index < count)
    (currentCanonical : GeneratedCanonicalQM31 current)
    (currentExact : (2 : ExactQM31) ^ index.val *
      generatedQm31ToExact current = generatedQm31ToExact initial)
    (halfRun : field.QM31.half current = ok next)
    (nextCanonical : GeneratedCanonicalQM31 next)
    (nextHalf : generatedQm31ToExact next + generatedQm31ToExact next =
      generatedQm31ToExact current) :
    let nextIndex := Std.U8.wrapping_add index 1#u8
    sumcheck.WeightAccumulator.impl.halve_qm31_loop.body
        count current index = ok (cont (next, nextIndex)) ∧
      nextIndex.val = index.val + 1 ∧
      GeneratedCanonicalQM31 next ∧
      (2 : ExactQM31) ^ nextIndex.val * generatedQm31ToExact next =
        generatedQm31ToExact initial := by
  let nextIndex := Std.U8.wrapping_add index 1#u8
  have nextIndexExact : nextIndex.val = index.val + 1 :=
    wrappingSuccExact index count active
  refine ⟨?_, nextIndexExact, nextCanonical, ?_⟩
  · unfold sumcheck.WeightAccumulator.impl.halve_qm31_loop.body
    rw [if_pos active, halfRun]
    simp only [bind_tc_ok, Std.lift]
  · rw [nextIndexExact, pow_succ]
    calc
      (2 : ExactQM31) ^ index.val * 2 * generatedQm31ToExact next =
          (2 : ExactQM31) ^ index.val *
            (generatedQm31ToExact next + generatedQm31ToExact next) := by ring
      _ = (2 : ExactQM31) ^ index.val * generatedQm31ToExact current := by
        rw [nextHalf]
      _ = generatedQm31ToExact initial := currentExact

private theorem halveBodyDone
    (count : Std.U8) (value : RawQM31) (index : Std.U8)
    (done : ¬ index < count) :
    sumcheck.WeightAccumulator.impl.halve_qm31_loop.body count value index =
      ok (ControlFlow.done value) := by
  unfold sumcheck.WeightAccumulator.impl.halve_qm31_loop.body
  rw [if_neg done]

theorem generated_halve_qm31_corresponds
    (value : RawQM31) (count : Std.U8)
    (canonical : GeneratedCanonicalQM31 value) :
    ∃ out,
      sumcheck.WeightAccumulator.impl.halve_qm31 value count = ok out ∧
      GeneratedCanonicalQM31 out ∧
      (2 : ExactQM31) ^ count.val * generatedQm31ToExact out =
        generatedQm31ToExact value := by
  have loopSpec :
      sumcheck.WeightAccumulator.impl.halve_qm31_loop value count 0#u8
        ⦃ out => GeneratedCanonicalQM31 out ∧
          (2 : ExactQM31) ^ count.val * generatedQm31ToExact out =
            generatedQm31ToExact value ⦄ := by
    unfold sumcheck.WeightAccumulator.impl.halve_qm31_loop
    apply loop.spec_decr_nat
      (fun state : RawQM31 × Std.U8 => count.val - state.2.val)
      (fun state => state.2.val ≤ count.val ∧
        GeneratedCanonicalQM31 state.1 ∧
        (2 : ExactQM31) ^ state.2.val * generatedQm31ToExact state.1 =
          generatedQm31ToExact value)
      (fun out => GeneratedCanonicalQM31 out ∧
        (2 : ExactQM31) ^ count.val * generatedQm31ToExact out =
          generatedQm31ToExact value)
    · rintro ⟨current, index⟩ ⟨indexBound, currentCanonical, currentExact⟩
      dsimp only at indexBound currentCanonical currentExact ⊢
      by_cases active : index < count
      · obtain ⟨next, halfRun, nextCanonical, nextHalf⟩ :=
          generated_qm31_half_corresponds current currentCanonical
        obtain ⟨bodyRun, nextIndexExact, nextCanonical, nextExact⟩ :=
          halveBodyActive value current next count index active
            currentCanonical currentExact halfRun nextCanonical nextHalf
        rw [bodyRun]
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨⟨?_, nextCanonical, nextExact⟩, ?_⟩ <;>
          rw [nextIndexExact] <;>
          rw [UScalar.lt_equiv] at active <;> omega
      · have atEnd : index.val = count.val := by
          rw [UScalar.lt_equiv] at active
          omega
        rw [halveBodyDone count current index active]
        simpa [atEnd] using And.intro currentCanonical currentExact
    · refine ⟨by norm_num, canonical, ?_⟩
      simp
  obtain ⟨out, run, outCanonical, outExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists loopSpec
  exact ⟨out, by
    unfold sumcheck.WeightAccumulator.impl.halve_qm31
    exact run, outCanonical, outExact⟩

#print axioms generated_halve_qm31_corresponds

end V7CallerCurrentReleaseR26TerminalLineHalving
