import V7CallerCurrentReleaseR30FixedFieldCanonical
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Canonicality of one accepted transcript-challenge limb

The generated retry loop masks every candidate with the M31 modulus and only
stores it when it differs from that modulus.  This proof follows the exact
symbolic loop trace and records the canonicality of the selected limb.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30ChallengeInnerCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev Transcript := transcript.Transcript
abbrev Limbs := Array field.M31 4#usize
abbrev Block := Array Std.U8 32#usize
abbrev InnerState := Transcript × Block × Std.Usize × Std.U32
abbrev InnerOutput := Transcript × Limbs × Block × Std.Usize × Bool

local instance : Inhabited field.M31 := ⟨field.M31.ZERO⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

def innerBody (limbs : Limbs) (limbIndex : Std.Usize)
    (state : InnerState) : Result (ControlFlow InnerState InnerOutput) :=
  transcript.Transcript.impl.challenge_qm31_loop0_loop0.body limbs limbIndex
    state.1 state.2.1 state.2.2.1 state.2.2.2

private theorem masked_canonical
    (word masked : Std.U32)
    (maskedRun : Aeneas.Std.lift (word &&& field.P) = ok masked)
    (accepted : (masked != field.P) = true) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 masked := by
  have maskedExact : masked = word &&& field.P := by
    simpa [Aeneas.Std.lift] using maskedRun.symm
  have bounded : masked.val ≤ field.P.val := by
    rw [maskedExact]
    exact Nat.and_le_right
  have distinct : masked.val ≠ field.P.val := by
    intro valuesExact
    have scalarsExact : masked = field.P := UScalar.eq_of_val_eq valuesExact
    have scalarsDistinct : masked ≠ field.P := by
      simpa using accepted
    exact scalarsDistinct scalarsExact
  unfold AspisAeneasCM31Multiplicative.CanonicalRawM31
    AspisAeneasCM31Multiplicative.m31Modulus
  simpa [field.P] using Nat.lt_of_le_of_ne bounded distinct

private def afterRefillBody (limbs : Limbs) (limbIndex : Std.Usize)
    (retryIndex : Std.U32) (self : Transcript) (block : Block)
    (wordIndex : Std.Usize) :
    Result (ControlFlow InnerState InnerOutput) := do
  let i ← lift (Std.Usize.wrapping_mul wordIndex 4#usize)
  let i1 ← lift (Std.Usize.wrapping_mul wordIndex 4#usize)
  let i2 ← lift (Std.Usize.wrapping_add i1 4#usize)
  let slice ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) block
      { start := i, «end» := i2 }
  let copied ←
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 slice
  let bytes ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError copied
  let word ← lift (core.num.U32.from_le_bytes bytes)
  let wordIndexOut ← lift (Std.Usize.wrapping_add wordIndex 1#usize)
  let masked ← lift (word &&& field.P)
  if masked != field.P then
    let limbsOut ← Array.update limbs limbIndex masked
    ok (done (self, limbsOut, block, wordIndexOut, true))
  else
    let retryIndexOut ← lift (Std.U32.wrapping_add retryIndex 1#u32)
    ok (cont (self, block, wordIndexOut, retryIndexOut))

private theorem after_refill_done_true_canonical_at_index
    (limbs : Limbs) (limbIndex : Std.Usize)
    (limbBound : limbIndex.val < 4)
    (retryIndex : Std.U32) (self : Transcript) (block : Block)
    (wordIndex : Std.Usize) (output : InnerOutput)
    (edge :
      afterRefillBody limbs limbIndex retryIndex self block wordIndex =
        ok (done output))
    :
    AspisAeneasCM31Multiplicative.CanonicalRawM31
        output.2.1.val[limbIndex.val]! ∧
      ∀ other, other < 4 → other ≠ limbIndex.val →
        output.2.1.val[other]! = limbs.val[other]! := by
  unfold afterRefillBody at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨i, iRun, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨i1, i1Run, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨i2, i2Run, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨slice, sliceRun, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨copied, copiedRun, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨bytes, bytesRun, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨word, wordRun, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨wordIndexOut, wordIndexRun, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨masked, maskedRun, edge⟩ := edge
  split at edge
  · rename_i acceptedMask
    rw [bind_eq_ok_iff] at edge
    obtain ⟨limbsOut, updateRun, edge⟩ := edge
    have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
    rw [← outputExact]
    have canonical := masked_canonical word masked maskedRun acceptedMask
    obtain ⟨expected, expectedRun, expectedExact⟩ := Aeneas.Std.WP.spec_imp_exists
      (Array.update_spec limbs limbIndex masked (by
        simpa [Array.length_eq] using limbBound))
    have limbsOutExact : limbsOut = expected :=
      Result.ok.inj (updateRun.symm.trans expectedRun)
    rw [limbsOutExact, expectedExact]
    constructor
    · simp only [Array.set_val_eq]
      rw [List.set_getElem!_eq _ _ _ _ (by
        exact ⟨by simpa [Array.length_eq] using limbBound, rfl⟩)]
      exact canonical
    · intro other otherBound distinct
      simp only [Array.set_val_eq]
      exact List.set_getElem!_ne _ _ _ _ (by omega)
  · cases edge

private theorem done_true_canonical_at_index
    (limbs : Limbs) (limbIndex : Std.Usize)
    (limbBound : limbIndex.val < 4)
    (state : InnerState) (output : InnerOutput)
    (edge : innerBody limbs limbIndex state = ok (done output))
    (accepted : output.2.2.2.2 = true) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31
        output.2.1.val[limbIndex.val]! ∧
      ∀ other, other < 4 → other ≠ limbIndex.val →
        output.2.1.val[other]! = limbs.val[other]! := by
  rcases state with ⟨self, block, wordIndex, retryIndex⟩
  unfold innerBody at edge
  unfold transcript.Transcript.impl.challenge_qm31_loop0_loop0.body at edge
  split at edge
  · split at edge
    · rw [bind_eq_ok_iff] at edge
      obtain ⟨refill, refillRun, edge⟩ := edge
      rcases refill with ⟨blockOut, selfOut⟩
      simp only [bind_tc_ok] at edge
      change
        afterRefillBody limbs limbIndex retryIndex selfOut blockOut 0#usize =
          ok (done output) at edge
      exact after_refill_done_true_canonical_at_index limbs limbIndex limbBound
        retryIndex selfOut blockOut 0#usize output edge
    · simp only [bind_tc_ok] at edge
      change
        afterRefillBody limbs limbIndex retryIndex self block wordIndex =
          ok (done output) at edge
      exact after_refill_done_true_canonical_at_index limbs limbIndex limbBound
        retryIndex self block wordIndex output edge
  · have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
    rw [← outputExact] at accepted
    simp at accepted

private theorem trace_true_canonical_at_index
    (limbs : Limbs) (limbIndex : Std.Usize)
    (limbBound : limbIndex.val < 4)
    {state : InnerState} {output : InnerOutput}
    (trace : ExactLoopTrace (innerBody limbs limbIndex) state output)
    (accepted : output.2.2.2.2 = true) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31
        output.2.1.val[limbIndex.val]! ∧
      ∀ other, other < 4 → other ≠ limbIndex.val →
        output.2.1.val[other]! = limbs.val[other]! := by
  induction trace with
  | done edge =>
      exact done_true_canonical_at_index limbs limbIndex limbBound _ _ edge
        accepted
  | cont edge tail inductionHypothesis =>
      exact inductionHypothesis accepted

theorem accepted_retry_loop_limb_canonical
    (self selfOut : Transcript) (limbs limbsOut : Limbs)
    (block blockOut : Block) (wordIndex wordIndexOut limbIndex : Std.Usize)
    (limbBound : limbIndex.val < 4)
    (run :
      transcript.Transcript.impl.challenge_qm31_loop0_loop0 self limbs block
          wordIndex limbIndex 0#u32 =
        ok (selfOut, limbsOut, blockOut, wordIndexOut, true)) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31
      limbsOut.val[limbIndex.val]! := by
  unfold transcript.Transcript.impl.challenge_qm31_loop0_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (innerBody limbs limbIndex)
    (self, block, wordIndex, 0#u32)
    (selfOut, limbsOut, blockOut, wordIndexOut, true) run
  exact (trace_true_canonical_at_index limbs limbIndex limbBound trace rfl).1

theorem accepted_retry_loop_other_limb_exact
    (self selfOut : Transcript) (limbs limbsOut : Limbs)
    (block blockOut : Block) (wordIndex wordIndexOut limbIndex : Std.Usize)
    (limbBound : limbIndex.val < 4)
    (run :
      transcript.Transcript.impl.challenge_qm31_loop0_loop0 self limbs block
          wordIndex limbIndex 0#u32 =
        ok (selfOut, limbsOut, blockOut, wordIndexOut, true))
    (other : Nat) (otherBound : other < 4)
    (distinct : other ≠ limbIndex.val) :
    limbsOut.val[other]! = limbs.val[other]! := by
  unfold transcript.Transcript.impl.challenge_qm31_loop0_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (innerBody limbs limbIndex)
    (self, block, wordIndex, 0#u32)
    (selfOut, limbsOut, blockOut, wordIndexOut, true) run
  exact (trace_true_canonical_at_index limbs limbIndex limbBound trace rfl).2
    other otherBound distinct

#print axioms accepted_retry_loop_limb_canonical
#print axioms accepted_retry_loop_other_limb_exact

end V7CallerCurrentReleaseR30ChallengeInnerCanonical
