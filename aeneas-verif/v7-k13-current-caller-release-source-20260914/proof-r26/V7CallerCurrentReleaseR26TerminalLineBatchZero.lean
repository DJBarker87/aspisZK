import V7CallerCurrentReleaseR26TerminalLineBatch

/-!
# Released terminal line batch from the zero accumulator

The optimized `dot` path initializes its line accumulator with zero arrays.
This specialization exposes the completed sixteen-line coefficient limbs,
canonicality, the exact line count, and the zero raw residue.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineBatchZero

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26TerminalLineRawLoop
open V7CallerCurrentReleaseR26TerminalLineLimbLoop
open V7CallerCurrentReleaseR26TerminalLineFlushLimb
open V7CallerCurrentReleaseR26TerminalLineReconstruction
open V7CallerCurrentReleaseR26TerminalLineStep
open V7CallerCurrentReleaseR26TerminalLineBatch

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def zeroLineConstant : Array RawM31 4#usize :=
  Array.repeat 4#usize field.M31.ZERO

def zeroLineRawRow : Array Std.U64 4#usize :=
  Array.repeat 4#usize 0#u64

def zeroLineRaw : Array (Array Std.U64 4#usize) 3#usize :=
  Array.repeat 3#usize zeroLineRawRow

def zeroLineSumRow : Array RawM31 4#usize :=
  Array.repeat 4#usize field.M31.ZERO

def zeroLineSums : Array (Array RawM31 4#usize) 3#usize :=
  Array.repeat 3#usize zeroLineSumRow

private theorem zeroCanonical : GeneratedCanonicalM31 field.M31.ZERO := by
  norm_num [GeneratedCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus, field.M31.ZERO]

@[simp] theorem zeroLineConstantCell
    (limb : Nat) (limbBound : limb < 4) :
    constantCell zeroLineConstant limb = field.M31.ZERO := by
  unfold constantCell zeroLineConstant
  rw [Array.repeat_val, List.getElem!_replicate _ (by simpa using limbBound)]

@[simp] theorem zeroLineRawCell
    (slot limb : Nat) (slotBound : slot < 3) (limbBound : limb < 4) :
    rawCell zeroLineRaw slot limb = 0#u64 := by
  unfold rawCell zeroLineRaw zeroLineRawRow
  rw [Array.repeat_val, List.getElem!_replicate _ (by simpa using slotBound)]
  rw [Array.repeat_val, List.getElem!_replicate _ (by simpa using limbBound)]

@[simp] theorem zeroLineSumCell
    (slot limb : Nat) (slotBound : slot < 3) (limbBound : limb < 4) :
    sumCell zeroLineSums slot limb = field.M31.ZERO := by
  unfold sumCell zeroLineSums zeroLineSumRow
  rw [Array.repeat_val, List.getElem!_replicate _ (by simpa using slotBound)]
  rw [Array.repeat_val, List.getElem!_replicate _ (by simpa using limbBound)]

theorem zero_line_state :
    LineAccumulatorStateInvariant 0 zeroLineConstant zeroLineRaw
      zeroLineSums := by
  refine ⟨?_, ?_, ?_⟩
  · intro limb limbBound
    rw [zeroLineConstantCell limb limbBound]
    exact zeroCanonical
  · intro slot slotBound limb limbBound
    rw [zeroLineSumCell slot limb slotBound limbBound]
    exact zeroCanonical
  · intro slot slotBound limb limbBound
    rw [zeroLineRawCell slot limb slotBound limbBound]
    norm_num

theorem generated_terminal_line_batch_zero_corresponds
    (deferred : Std.U8) (scales : Slice RawQM31) (xs : Slice RawM31)
    (scalesLength : scales.val.length = 16)
    (xsLength : xs.val.length = 16)
    (scalesCanonical : TerminalCanonicalQM31Slice scales)
    (xsCanonical : TerminalCanonicalM31Slice xs) :
    ∃ out,
      sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot
          deferred scales xs deferred 0#usize zeroLineConstant zeroLineRaw
            zeroLineSums = ok out ∧
      out.1.val = 16 ∧
      CanonicalFourLimbs out.2.1 ∧
      (∀ limb, limb < 4 →
        generatedM31ToExact (constantCell out.2.1 limb) =
          terminalConstantPrefix scales 16 limb) ∧
      CanonicalLineSums out.2.2.2 ∧
      (∀ slot, slot < 3 → ∀ limb, limb < 4 →
        (rawCell out.2.2.1 slot limb).val = 0) ∧
      (∀ slot, slot < 3 → ∀ limb, limb < 4 →
        generatedM31ToExact (sumCell out.2.2.2 slot limb) =
          terminalLinePrefix scales xs 16 slot limb) := by
  have loopSpec := generated_terminal_line_batch_loop_corresponds deferred
    scales xs zeroLineConstant zeroLineRaw zeroLineSums scalesLength xsLength
      scalesCanonical xsCanonical zero_line_state
  obtain ⟨out, loopRun, countExact, state, constantExact, lineExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists loopSpec
  have rawZero : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
      (rawCell out.2.2.1 slot limb).val = 0 := by
    intro slot slotBound limb limbBound
    have bound := state.2.2 slot slotBound limb limbBound
    norm_num at bound
    omega
  refine ⟨out, ?_, countExact, ?_, ?_, state.2.1, rawZero, ?_⟩
  · unfold sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot
    exact loopRun
  · simpa [CanonicalFourLimbs, CanonicalConstantLimbs, constantCell]
      using state.1
  · intro limb limbBound
    have exact := constantExact limb limbBound
    rw [zeroLineConstantCell limb limbBound] at exact
    simpa [generatedM31ToExact, field.M31.ZERO] using exact
  · intro slot slotBound limb limbBound
    have exact := lineExact slot slotBound limb limbBound
    rw [rawZero slot slotBound limb limbBound] at exact
    rw [zeroLineSumCell slot limb slotBound limbBound] at exact
    rw [zeroLineRawCell slot limb slotBound limbBound] at exact
    simpa [generatedM31ToExact, field.M31.ZERO] using exact

#print axioms zero_line_state
#print axioms generated_terminal_line_batch_zero_corresponds

end V7CallerCurrentReleaseR26TerminalLineBatchZero
