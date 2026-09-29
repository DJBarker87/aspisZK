import V7CallerCurrentReleaseR26TerminalLineFlushLimb

/-!
# Complete terminal line raw-buffer flush

This lifts the verified four-limb flush across all three line-basis slots.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineFlush

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26TerminalLineRawLoop
open V7CallerCurrentReleaseR26TerminalLineFlushLimb

abbrev RawM31 := field.M31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

def FlushSlotInvariant
    (baseRaw currentRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums currentSums : Array (Array RawM31 4#usize) 3#usize)
    (processed : Nat) : Prop :=
  CanonicalLineSums currentSums ∧
  (∀ slot, slot < 3 → ∀ limb, limb < 4 →
    (rawCell currentRaw slot limb).val =
      if slot < processed then 0 else (rawCell baseRaw slot limb).val) ∧
  (∀ slot, slot < 3 → ∀ limb, limb < 4 →
    generatedM31ToExact (sumCell currentSums slot limb) =
      if slot < processed then
        generatedM31ToExact (sumCell baseSums slot limb) +
          ((rawCell baseRaw slot limb).val : ExactM31)
      else generatedM31ToExact (sumCell baseSums slot limb))

private theorem flushSlotInvariantStep
    (baseRaw currentRaw nextRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums currentSums nextSums : Array (Array RawM31 4#usize) 3#usize)
    (slot : Std.Usize) (slotBound : slot.val < 3)
    (outer : FlushSlotInvariant baseRaw currentRaw baseSums currentSums
      slot.val)
    (inner : FlushLimbInvariant currentRaw nextRaw currentSums nextSums
      slot.val 4) :
    FlushSlotInvariant baseRaw nextRaw baseSums nextSums
      (slot.val + 1) := by
  rcases outer with ⟨outerCanonical, outerRaw, outerSums⟩
  rcases inner with ⟨innerCanonical, innerRaw, innerSums⟩
  refine ⟨innerCanonical, ?_, ?_⟩
  · intro row rowBound limb limbBound
    have innerCell := innerRaw row rowBound limb limbBound
    have outerCell := outerRaw row rowBound limb limbBound
    by_cases same : row = slot.val
    · subst row
      simp only [show limb < 4 from limbBound, and_self, if_pos] at innerCell
      rw [innerCell]
      simp
    · have frame : (rawCell nextRaw row limb).val =
          (rawCell currentRaw row limb).val := by
        simpa [same] using innerCell
      rw [frame, outerCell]
      by_cases before : row < slot.val
      · rw [if_pos before, if_pos (by omega)]
      · rw [if_neg before, if_neg (by omega)]
  · intro row rowBound limb limbBound
    have innerCell := innerSums row rowBound limb limbBound
    have outerCell := outerSums row rowBound limb limbBound
    by_cases same : row = slot.val
    · subst row
      simp only [show limb < 4 from limbBound, and_self, if_pos] at innerCell
      have outerRawCell := outerRaw slot.val slotBound limb limbBound
      rw [if_neg (by omega)] at outerRawCell
      rw [innerCell, outerCell, outerRawCell]
      simp
    · have frame : generatedM31ToExact (sumCell nextSums row limb) =
          generatedM31ToExact (sumCell currentSums row limb) := by
        simpa [same] using innerCell
      rw [frame, outerCell]
      by_cases before : row < slot.val
      · rw [if_pos before, if_pos (by omega)]
      · rw [if_neg before, if_neg (by omega)]

private theorem generatedFlushSlotBodyActive
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums : Array (Array RawM31 4#usize) 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (currentRaw : Array (Array Std.U64 4#usize) 3#usize)
    (currentSums : Array (Array RawM31 4#usize) 3#usize)
    (active : iter.start.val < iter.end.val) (endExact : iter.end.val = 3)
    (invariant : FlushSlotInvariant baseRaw currentRaw baseSums currentSums
      iter.start.val) :
    ∃ iter' nextRaw nextSums,
      sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2.body
          iter currentRaw currentSums =
        ok (cont (iter', nextRaw, nextSums)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      FlushSlotInvariant baseRaw nextRaw baseSums nextSums
        (iter.start.val + 1) := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter active
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have slotBound : iter.start.val < 3 := by omega
  have innerSpec := generated_line_flush_limb_loop_corresponds currentRaw
    currentSums iter.start slotBound invariant.1
  obtain ⟨out, innerRun, innerPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists innerSpec
  let nextRaw := out.1
  let nextSums := out.2
  refine ⟨iter', nextRaw, nextSums, ?_, startEq,
    congrArg UScalar.val endEq, ?_⟩
  · unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [innerRun]
    rfl
  · exact flushSlotInvariantStep baseRaw currentRaw nextRaw baseSums
      currentSums nextSums iter.start slotBound invariant innerPost

theorem generated_line_flush_corresponds
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums : Array (Array RawM31 4#usize) 3#usize)
    (baseSumsCanonical : CanonicalLineSums baseSums) :
    sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2
        { start := 0#usize, «end» := 3#usize } baseRaw baseSums
      ⦃ out => FlushSlotInvariant baseRaw out.1 baseSums out.2 3 ⦄ := by
  simp only [sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      (Array (Array Std.U64 4#usize) 3#usize ×
        Array (Array RawM31 4#usize) 3#usize) => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      FlushSlotInvariant baseRaw state.2.1 baseSums state.2.2
        state.1.start.val)
    (fun out : Array (Array Std.U64 4#usize) 3#usize ×
        Array (Array RawM31 4#usize) 3#usize =>
      FlushSlotInvariant baseRaw out.1 baseSums out.2 3)
  · rintro ⟨iter, currentRaw, currentSums⟩
      ⟨endExact, startBound, invariant⟩
    dsimp only at endExact startBound invariant ⊢
    by_cases active : iter.start.val < iter.end.val
    · obtain ⟨iter', nextRaw, nextSums, bodyRun, nextStart, nextEnd,
          nextInvariant⟩ :=
        generatedFlushSlotBodyActive baseRaw baseSums iter currentRaw
          currentSums active endExact invariant
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      have nextInvariant' : FlushSlotInvariant baseRaw nextRaw baseSums
          nextSums iter'.start.val := by
        rw [nextStart]
        exact nextInvariant
      refine ⟨⟨?_, ?_, nextInvariant'⟩, ?_⟩
      · rw [nextEnd]
        exact endExact
      · rw [nextStart]
        omega
      · rw [nextStart]
        omega
    · have done : iter.start.val = 3 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2.body
      rw [nextRun]
      simpa [done] using invariant
  · refine ⟨by norm_num, by norm_num, baseSumsCanonical, ?_, ?_⟩
    · intro slot slotBound limb limbBound
      simp
    · intro slot slotBound limb limbBound
      simp

#print axioms generated_line_flush_corresponds

end V7CallerCurrentReleaseR26TerminalLineFlush
