import V7CallerCurrentReleaseR30ChallengeInnerCanonical

/-!
# Canonicality of successful transcript QM31 challenges

This module lifts the accepted-limb theorem through the generated four-limb
loop and then through `Transcript::challenge_qm31` itself.  It follows exact
symbolic loop traces and does not reduce a concrete transcript state.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30ChallengeCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR30ChallengeInnerCanonical

abbrev Transcript := transcript.Transcript
abbrev Limbs := Array field.M31 4#usize
abbrev Block := Array Std.U8 32#usize
abbrev OuterState := Transcript × Limbs × Block × Std.Usize × Std.Usize
abbrev OuterOutput := Transcript × Limbs ×
  Option (core.result.Result field.QM31 transcript.ChallengeSampleExhausted)

local instance : Inhabited field.M31 := ⟨field.M31.ZERO⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

def outerBody (state : OuterState) :
    Result (ControlFlow OuterState OuterOutput) :=
  transcript.Transcript.impl.challenge_qm31_loop0.body
    state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2

def CanonicalPrefix (limbs : Limbs) (limbIndex : Std.Usize) : Prop :=
  ∀ index, index < limbIndex.val → index < 4 →
    AspisAeneasCM31Multiplicative.CanonicalRawM31 limbs.val[index]!

def CanonicalLimbs (limbs : Limbs) : Prop :=
  ∀ index, index < 4 →
    AspisAeneasCM31Multiplicative.CanonicalRawM31 limbs.val[index]!

private theorem to_slice_length_four
    (limbs : Limbs) (slice : Slice field.M31)
    (run : Aeneas.Std.lift (Array.to_slice limbs) = ok slice) :
    slice.length = 4 := by
  simpa [Aeneas.Std.lift, Array.to_slice, Array.length_eq] using
    congrArg Slice.length (Result.ok.inj run)

private theorem continuing_body_preserves_prefix
    (state next : OuterState)
    (edge : outerBody state = ok (cont next))
    (prefixCanonical : CanonicalPrefix state.2.1 state.2.2.2.2) :
    CanonicalPrefix next.2.1 next.2.2.2.2 := by
  rcases state with ⟨self, limbs, block, wordIndex, limbIndex⟩
  rcases next with ⟨selfOut, limbsOut, blockOut, wordIndexOut, limbIndexOut⟩
  change CanonicalPrefix limbs limbIndex at prefixCanonical
  change CanonicalPrefix limbsOut limbIndexOut
  unfold outerBody at edge
  unfold transcript.Transcript.impl.challenge_qm31_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨slice, sliceRun, edge⟩ := edge
  split at edge
  · rename_i active
    rw [bind_eq_ok_iff] at edge
    obtain ⟨retryOut, retryRun, edge⟩ := edge
    rcases retryOut with ⟨selfAfter, limbsAfter, blockAfter, wordIndexAfter,
      accepted⟩
    cases accepted
    · simp only at edge
      cases edge
    · simp only [if_true] at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨limbIndexAfter, incrementRun, edge⟩ := edge
      simp only [Result.ok.injEq, ControlFlow.cont.injEq,
        Prod.mk.injEq] at edge
      rcases edge with ⟨selfExact, limbsExact, blockExact, wordIndexExact,
        limbIndexExact⟩
      subst selfOut
      subst limbsOut
      subst blockOut
      subst wordIndexOut
      subst limbIndexOut
      have limbBound : limbIndex.val < 4 := by
        have lengthFour := to_slice_length_four limbs slice sliceRun
        simpa [lengthFour] using active
      have currentCanonical := accepted_retry_loop_limb_canonical
        self selfAfter limbs limbsAfter block blockAfter wordIndex wordIndexAfter
        limbIndex limbBound retryRun
      have usizeBound : limbIndex.val + 1 < Usize.size := by
        have literalBound := UScalar.hSize (4#usize)
        have fourBound : 4 < Usize.size := by
          simpa [UScalar.size_UScalarTyUsize] using literalBound
        omega
      have incrementExact : limbIndexAfter.val = limbIndex.val + 1 := by
        have moduloExact :
            (limbIndex.val + 1) % Usize.size = limbIndexAfter.val := by
          simpa [Aeneas.Std.lift, Std.Usize.wrapping_add] using
            congrArg UScalar.val (Result.ok.inj incrementRun)
        rw [Nat.mod_eq_of_lt usizeBound] at moduloExact
        exact moduloExact.symm
      intro index indexBefore indexBound
      rw [incrementExact] at indexBefore
      by_cases current : index = limbIndex.val
      · subst index
        exact currentCanonical
      · have old : index < limbIndex.val := by omega
        rw [accepted_retry_loop_other_limb_exact
          self selfAfter limbs limbsAfter block blockAfter wordIndex
          wordIndexAfter limbIndex limbBound retryRun index indexBound current]
        exact prefixCanonical index old indexBound
  · cases edge

private theorem done_none_exposes_complete_prefix
    (state : OuterState) (output : OuterOutput)
    (edge : outerBody state = ok (done output))
    (pendingNone : output.2.2 = none) :
    output.2.1 = state.2.1 ∧
      ∀ index, index < 4 → index < state.2.2.2.2.val := by
  rcases state with ⟨self, limbs, block, wordIndex, limbIndex⟩
  change output.2.1 = limbs ∧
    ∀ index, index < 4 → index < limbIndex.val
  unfold outerBody at edge
  unfold transcript.Transcript.impl.challenge_qm31_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨slice, sliceRun, edge⟩ := edge
  split at edge
  · rw [bind_eq_ok_iff] at edge
    obtain ⟨retryOut, retryRun, edge⟩ := edge
    rcases retryOut with ⟨selfAfter, limbsAfter, blockAfter, wordIndexAfter,
      accepted⟩
    cases accepted
    · simp only at edge
      have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← outputExact] at pendingNone
      simp at pendingNone
    · simp only [if_true] at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨limbIndexAfter, incrementRun, edge⟩ := edge
      cases edge
  · rename_i inactive
    have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
    rw [← outputExact]
    constructor
    · rfl
    · intro index indexBound
      have lengthFour := to_slice_length_four limbs slice sliceRun
      have notActive : ¬ limbIndex.val < 4 := by
        simpa [lengthFour] using inactive
      omega

private theorem done_pending_classification
    (state : OuterState) (output : OuterOutput)
    (edge : outerBody state = ok (done output)) :
    output.2.2 = none ∨
      ∃ error : transcript.ChallengeSampleExhausted,
        output.2.2 = some (.Err error) := by
  rcases state with ⟨self, limbs, block, wordIndex, limbIndex⟩
  unfold outerBody at edge
  unfold transcript.Transcript.impl.challenge_qm31_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨slice, sliceRun, edge⟩ := edge
  split at edge
  · rw [bind_eq_ok_iff] at edge
    obtain ⟨retryOut, retryRun, edge⟩ := edge
    rcases retryOut with ⟨selfAfter, limbsAfter, blockAfter, wordIndexAfter,
      accepted⟩
    cases accepted
    · simp only at edge
      have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← outputExact]
      exact Or.inr ⟨(), rfl⟩
    · simp only [if_true] at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨limbIndexAfter, incrementRun, edge⟩ := edge
      cases edge
  · have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
    rw [← outputExact]
    exact Or.inl rfl

private theorem trace_none_canonical
    {state : OuterState} {output : OuterOutput}
    (trace : ExactLoopTrace outerBody state output)
    (prefixCanonical : CanonicalPrefix state.2.1 state.2.2.2.2)
    (pendingNone : output.2.2 = none) :
    CanonicalLimbs output.2.1 := by
  induction trace with
  | done edge =>
      obtain ⟨limbsExact, complete⟩ :=
        done_none_exposes_complete_prefix _ _ edge pendingNone
      rw [limbsExact]
      intro index indexBound
      exact prefixCanonical index (complete index indexBound) indexBound
  | @cont _ next _ edge tail inductionHypothesis =>
      exact inductionHypothesis
        (continuing_body_preserves_prefix _ next edge prefixCanonical) pendingNone

private theorem trace_pending_classification
    {state : OuterState} {output : OuterOutput}
    (trace : ExactLoopTrace outerBody state output) :
    output.2.2 = none ∨
      ∃ error : transcript.ChallengeSampleExhausted,
        output.2.2 = some (.Err error) := by
  induction trace with
  | done edge => exact done_pending_classification _ _ edge
  | cont edge tail inductionHypothesis => exact inductionHypothesis

theorem successful_challenge_limb_loop_canonical
    (self selfOut : Transcript) (limbs limbsOut : Limbs)
    (block : Block) (wordIndex limbIndex : Std.Usize)
    (pending : Option
      (core.result.Result field.QM31 transcript.ChallengeSampleExhausted))
    (prefixCanonical : CanonicalPrefix limbs limbIndex)
    (run :
      transcript.Transcript.impl.challenge_qm31_loop0 self limbs block
          wordIndex limbIndex = ok (selfOut, limbsOut, pending))
    (pendingNone : pending = none) :
    CanonicalLimbs limbsOut := by
  unfold transcript.Transcript.impl.challenge_qm31_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace outerBody
    (self, limbs, block, wordIndex, limbIndex)
    (selfOut, limbsOut, pending) run
  exact trace_none_canonical trace prefixCanonical pendingNone

theorem successful_challenge_limb_loop_pending_classification
    (self selfOut : Transcript) (limbs limbsOut : Limbs)
    (block : Block) (wordIndex limbIndex : Std.Usize)
    (pending : Option
      (core.result.Result field.QM31 transcript.ChallengeSampleExhausted))
    (run :
      transcript.Transcript.impl.challenge_qm31_loop0 self limbs block
          wordIndex limbIndex = ok (selfOut, limbsOut, pending)) :
    pending = none ∨
      ∃ error : transcript.ChallengeSampleExhausted,
        pending = some (.Err error) := by
  unfold transcript.Transcript.impl.challenge_qm31_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace outerBody
    (self, limbs, block, wordIndex, limbIndex)
    (selfOut, limbsOut, pending) run
  exact trace_pending_classification trace

theorem successful_challenge_qm31_canonical
    (self selfOut : Transcript) (value : field.QM31)
    (run : transcript.Transcript.impl.challenge_qm31 self =
      ok (.Ok value, selfOut)) :
    GeneratedCanonicalQM31 value := by
  unfold transcript.Transcript.impl.challenge_qm31 at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨squeezed, squeezeRun, run⟩ := run
  rcases squeezed with ⟨block, selfAfterSqueeze⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨loopOut, loopRun, run⟩ := run
  rcases loopOut with ⟨selfAfterLoop, limbsOut, pending⟩
  have classification := successful_challenge_limb_loop_pending_classification
    selfAfterSqueeze selfAfterLoop (Array.repeat 4#usize field.M31.ZERO)
    limbsOut block 0#usize 0#usize pending loopRun
  rcases classification with pendingNone | ⟨error, pendingError⟩
  · subst pending
    have limbsCanonical := successful_challenge_limb_loop_canonical
      selfAfterSqueeze selfAfterLoop (Array.repeat 4#usize field.M31.ZERO)
      limbsOut block 0#usize 0#usize none (by
        intro index before
        simp at before) loopRun rfl
    rw [bind_eq_ok_iff] at run
    obtain ⟨m0, m0Run, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m1, m1Run, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m2, m2Run, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨m3, m3Run, run⟩ := run
    simp only [Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Ok.injEq] at run
    rcases run with ⟨valueExact, selfExact⟩
    rw [← valueExact]
    unfold GeneratedCanonicalQM31 GeneratedCanonicalCM31
    have c0 := limbsCanonical 0 (by omega)
    have c1 := limbsCanonical 1 (by omega)
    have c2 := limbsCanonical 2 (by omega)
    have c3 := limbsCanonical 3 (by omega)
    simp [Array.index_usize] at m0Run m1Run m2Run m3Run
    subst m0
    subst m1
    subst m2
    subst m3
    simpa [List.getElem!_eq_getElem?_getD] using
      And.intro (And.intro c0 c1) (And.intro c2 c3)
  · rw [pendingError] at run
    simp at run

#print axioms successful_challenge_limb_loop_canonical
#print axioms successful_challenge_qm31_canonical

end V7CallerCurrentReleaseR30ChallengeCanonical
