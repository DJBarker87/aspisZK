import V7CallerCurrentReleaseR26Qm31DotReconstruction
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Exact nine-channel reduction loop for the current QM31 dot product

Each four-input raw chunk is reduced into the nine canonical M31 channel
accumulators.  This proof treats that fixed reduction loop independently of
the raw multiplication loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotReductionLoop

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotReconstruction

abbrev M31 := field.M31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited M31 := ⟨field.M31.ZERO⟩
local instance : Inhabited Std.U64 := ⟨0#u64⟩

def ReducedChannelInvariant
    (base current : Array M31 9#usize) (raw : Array Std.U64 9#usize)
    (processed : Nat) : Prop :=
  CanonicalDotChannels current ∧
    ∀ channel, channel < 9 →
      generatedM31ToExact current.val[channel]! =
        generatedM31ToExact base.val[channel]! +
          if channel < processed then (raw.val[channel]!.val : ExactM31)
          else 0

private theorem array_index_run {T : Type} [Inhabited T]
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (bound : index.val < values.length) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index bound)
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

private theorem array_update_eq_set {T : Type}
    {n : Std.Usize} (values updated : Array T n)
    (index : Std.Usize) (value : T)
    (bound : index.val < n.val)
    (run : values.update index value = ok updated) :
    updated = values.set index value := by
  have spec := Array.update_spec values index value (by
    simpa [Array.length_eq] using bound)
  obtain ⟨expected, expectedRun, expectedExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists spec
  have outputExact : updated = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  exact outputExact.trans expectedExact

private theorem set_same {T : Type} [Inhabited T]
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (value : T) (bound : index.val < n.val) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using bound, rfl⟩

private theorem set_ne {T : Type} [Inhabited T]
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (value : T) (other : Nat) (different : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  apply List.set_getElem!_ne
  omega

private theorem reduction_body_active
    (base sums : Array M31 9#usize) (raw : Array Std.U64 9#usize)
    (iter nextIter : core.ops.range.Range Std.Usize)
    (index : Std.Usize)
    (iteratorRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        ok (some index, nextIter))
    (invariant : ReducedChannelInvariant base sums raw iter.start.val)
    (endExact : iter.end.val = 9) :
    ∃ sumsNext,
      field.qm31_dot_loop0_loop1.body raw iter sums =
        ok (cont (nextIter, sumsNext)) ∧
      ReducedChannelInvariant base sumsNext raw nextIter.start.val := by
  obtain ⟨active, indexExact, nextStart, sameEnd⟩ :=
    range_next_some_exact iter nextIter index iteratorRun
  have indexBound : index.val < 9 := by rw [indexExact]; omega
  have sumsRead := array_index_run sums index (by
    simpa [Array.length_eq] using indexBound)
  have rawRead := array_index_run raw index (by
    simpa [Array.length_eq] using indexBound)
  let prior := sums.val[index.val]!
  let rawValue := raw.val[index.val]!
  have priorCanonical : GeneratedCanonicalM31 prior :=
    invariant.1 index.val indexBound
  obtain ⟨reduced, reducedRun, reducedCanonical, reducedExact⟩ :=
    generated_m31_reduce_u64_corresponds rawValue
  obtain ⟨next, nextRun, nextCanonical, nextExact⟩ :=
    generated_m31_add_corresponds prior reduced priorCanonical reducedCanonical
  obtain ⟨sumsNext, updateRun, updateExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.update_spec sums index next (by
        simpa [Array.length_eq] using indexBound))
  have sumsNextSet : sumsNext = sums.set index next :=
    array_update_eq_set sums sumsNext index next indexBound updateRun
  refine ⟨sumsNext, ?_, ?_⟩
  · unfold field.qm31_dot_loop0_loop1.body
    rw [iteratorRun]
    simp only [bind_tc_ok]
    rw [sumsRead, rawRead]
    simp only [bind_tc_ok]
    rw [reducedRun]
    simp only [bind_tc_ok]
    change
      (do
        let m2 ← field.M31.add prior reduced
        let a ← sums.update index m2
        ok (cont (nextIter, a))) = _
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [updateRun]
    simp
  · rw [sumsNextSet]
    constructor
    · intro channel channelBound
      by_cases same : channel = index.val
      · subst channel
        rw [set_same sums index next indexBound]
        exact nextCanonical
      · rw [set_ne sums index next channel same]
        exact invariant.1 channel channelBound
    · intro channel channelBound
      by_cases same : channel = index.val
      · subst channel
        rw [set_same sums index next indexBound]
        have nextExact' : generatedM31ToExact next =
            generatedM31ToExact prior + generatedM31ToExact reduced := by
          simpa [generatedM31ToExact] using nextExact
        rw [nextExact', reducedExact]
        have oldExact := invariant.2 index.val indexBound
        rw [oldExact, indexExact, nextStart]
        rw [if_neg (by omega : ¬ iter.start.val < iter.start.val)]
        rw [if_pos (by omega : iter.start.val < iter.start.val + 1)]
        simp only [rawValue]
        rw [indexExact]
        ring
      · rw [set_ne sums index next channel same]
        have oldExact := invariant.2 channel channelBound
        rw [oldExact, nextStart]
        have indexVal : index.val = iter.start.val :=
          congrArg UScalar.val indexExact
        by_cases before : channel < iter.start.val
        · rw [if_pos before, if_pos (by omega)]
        · have after : ¬ channel < iter.start.val + 1 := by
            intro h
            have : channel = iter.start.val := by omega
            exact same (this.trans indexVal.symm)
          rw [if_neg before, if_neg after]

private theorem reduction_body_done
    (raw : Array Std.U64 9#usize)
    (iter : core.ops.range.Range Std.Usize) (sums : Array M31 9#usize)
    (iteratorRun :
      ∃ iterAfter,
        core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
          ok (none, iterAfter)) :
    field.qm31_dot_loop0_loop1.body raw iter sums = ok (done sums) := by
  obtain ⟨iterAfter, run⟩ := iteratorRun
  unfold field.qm31_dot_loop0_loop1.body
  rw [run]
  simp

/-- The generated range loop reduces all nine raw channels into canonical
M31 accumulators with their exact field meaning. -/
theorem generated_dot_reduction_loop_corresponds
    (base sums : Array M31 9#usize) (raw : Array Std.U64 9#usize)
    (iter : core.ops.range.Range Std.Usize)
    (endExact : iter.end.val = 9)
    (startBound : iter.start.val ≤ 9)
    (invariant : ReducedChannelInvariant base sums raw iter.start.val) :
    field.qm31_dot_loop0_loop1 iter sums raw
      ⦃ out => ReducedChannelInvariant base out raw 9 ⦄ := by
  simp only [field.qm31_dot_loop0_loop1]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize × Array M31 9#usize =>
      9 - state.1.start.val)
    (fun state => state.1.end.val = 9 ∧
      state.1.start.val ≤ 9 ∧
      ReducedChannelInvariant base state.2 raw state.1.start.val)
    (fun out => ReducedChannelInvariant base out raw 9)
  · rintro ⟨currentIter, current⟩ ⟨currentEnd, startBound, currentInvariant⟩
    dsimp only at currentEnd startBound currentInvariant ⊢
    by_cases active : currentIter.start.val < currentIter.end.val
    · obtain ⟨⟨option, nextIter⟩, iteratorRun, optionExact,
          nextStart, nextEnd⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_some_spec
            currentIter active)
      rw [optionExact] at iteratorRun
      obtain ⟨next, bodyRun, nextInvariant⟩ :=
        reduction_body_active base current raw currentIter nextIter
          currentIter.start iteratorRun currentInvariant currentEnd
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, by omega, nextInvariant⟩, ?_⟩
      · rw [nextEnd, currentEnd]
      · rw [nextStart]
        omega
    · have finished : currentIter.end.val ≤ currentIter.start.val := by omega
      obtain ⟨⟨option, nextIter⟩, iteratorRun, optionExact, _nextExact⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_none_spec
            currentIter finished)
      rw [optionExact] at iteratorRun
      have atEnd : currentIter.start.val = 9 := by omega
      rw [reduction_body_done raw currentIter current
        ⟨nextIter, iteratorRun⟩]
      simpa [atEnd] using currentInvariant
  · exact ⟨endExact, startBound, invariant⟩

/-- Starting at channel zero, the fixed generated reduction loop adds every
raw residue exactly once. -/
theorem generated_dot_reduction_all_channels
    (base : Array M31 9#usize) (raw : Array Std.U64 9#usize)
    (baseCanonical : CanonicalDotChannels base) :
    field.qm31_dot_loop0_loop1
        { start := 0#usize, «end» := 9#usize } base raw
      ⦃ out => CanonicalDotChannels out ∧
        ∀ channel, channel < 9 →
          generatedM31ToExact out.val[channel]! =
            generatedM31ToExact base.val[channel]! +
              (raw.val[channel]!.val : ExactM31) ⦄ := by
  obtain ⟨out, outRun, outExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (generated_dot_reduction_loop_corresponds base base raw
      { start := 0#usize, «end» := 9#usize } (by norm_num) (by norm_num) (by
        refine ⟨baseCanonical, ?_⟩
        intro channel channelBound
        simp))
  rw [outRun]
  simp only [Aeneas.Std.WP.spec_ok]
  refine ⟨outExact.1, ?_⟩
  intro channel channelBound
  simpa [ReducedChannelInvariant, channelBound] using
    outExact.2 channel channelBound

#print axioms generated_dot_reduction_loop_corresponds
#print axioms generated_dot_reduction_all_channels

end V7CallerCurrentReleaseR26Qm31DotReductionLoop
