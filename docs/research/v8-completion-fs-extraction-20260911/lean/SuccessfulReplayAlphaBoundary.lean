import FSLivePrefixMiddleComponents
import ExtractionCollectorSuccessfulReplay
import FSLiveAlphaBoundary

/-!
# An accepted same-body replay constructs its actual alpha boundary

This leaf removes an analysis-only alpha transcript from the replay path. It
decomposes one successful selected replay into its literal source/OOD/gamma
run and literal source-functional middle run, then constructs the actual alpha
candidate call made from that same body, tape, and threaded oracle state.

It does not say that a requested programmed alpha target equals this actual
input. That equality-or-target-hit classification remains the next
Fiat--Shamir obligation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.SuccessfulReplayAlphaBoundary

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorSuccessfulReplay
open FSLivePrefixMiddleComponents
open FSLiveAlphaBoundary
open FSNonzeroQM31
open FSV8AlphaChallengeInputBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

noncomputable section

/-- All alpha-boundary data below are constructed from one successful replay.
The record equality says that the staged prefix is the prefix retained by the
replay's authenticated suffix; it is not a caller-supplied coherence
assumption.  This is a proposition so successful script eliminators may
construct the existential witnesses without a choice axiom at the interface. -/
def ActualAlphaRun {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork) : Prop :=
  ∃ staged : Partial replay.body z, ∃ prefixDigest middleDigest : Block,
    let sourceState :=
      (run replay.tape
        (sourceThenGammaScript firstWork secondWork replay.body initialDigest)
        replay.oracle).2
    let boundary := alphaBoundary staged.out staged.gamma replay.body z
      prefixDigest replay.tape sourceState staged.middle
    replay.record =
        { out := staged.out
          gamma := staged.gamma
          middle := staged.middle
          suffix := replay.record.suffix } ∧
      (run replay.tape
        (sourceThenGammaScript firstWork secondWork replay.body initialDigest)
        replay.oracle).1 = some (.ok (staged.out, staged.gamma), prefixDigest) ∧
      (run replay.tape
        (middleScript staged.out staged.gamma replay.body z prefixDigest)
        sourceState).1 = some (.ok staged.middle, middleDigest) ∧
      (run replay.tape (candidateScript boundary.digest) boundary.oracle).1 =
        some (.ok staged.middle.middle.alpha0,
          (candidate replay.tape boundary).2.digest) ∧
      staged.middle.middle.alpha0 = replay.record.middle.middle.alpha0 ∧
      ∃ event,
        event.input = alphaCandidateInput boundary ∧
        event ∈
          (run replay.tape (candidateScript boundary.digest) boundary.oracle).2.log

/-- `afterAlphaNonce` is the literal transcript state reached by the same
successful replay immediately before its first alpha candidate request.  The
source and middle runs are retained in the predicate, so a later restoration
configuration cannot substitute an analysis-only transcript. -/
def IsActualAlphaBoundary {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork)
    (afterAlphaNonce : FSBoundedTranscript.Transcript) : Prop :=
  ∃ staged : Partial replay.body z, ∃ prefixDigest middleDigest : Block,
    let sourceState :=
      (run replay.tape
        (sourceThenGammaScript firstWork secondWork replay.body initialDigest)
        replay.oracle).2
    replay.record =
        { out := staged.out
          gamma := staged.gamma
          middle := staged.middle
          suffix := replay.record.suffix } ∧
      (run replay.tape
        (sourceThenGammaScript firstWork secondWork replay.body initialDigest)
        replay.oracle).1 = some (.ok (staged.out, staged.gamma), prefixDigest) ∧
      (run replay.tape
        (middleScript staged.out staged.gamma replay.body z prefixDigest)
        sourceState).1 = some (.ok staged.middle, middleDigest) ∧
      afterAlphaNonce = alphaBoundary staged.out staged.gamma replay.body z
        prefixDigest replay.tape sourceState staged.middle

/-- A successful selected replay constructs its source-threaded actual alpha
run. In particular, neither the middle program nor the alpha query is supplied
independently of the replay body. -/
theorem successful_replay_constructs_actual_alpha_run
    {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork) :
    ActualAlphaRun replay := by
  unfold ActualAlphaRun
  obtain ⟨staged, middleDigest, prefixSuccess, suffixSuccess⟩ :=
    successful_wholeStaged_components firstWork secondWork z cuts replay.body
      initialDigest replay.tape replay.oracle replay.record replay.finalDigest
      replay.success
  obtain ⟨prefixDigest, sourceSuccess, middleSuccess⟩ :=
    successful_prefix_middle_components firstWork secondWork z replay.body
      initialDigest replay.tape replay.oracle staged middleDigest prefixSuccess
  have recordEq := successful_suffix_retains_partial cuts replay.body z
    middleDigest staged replay.tape
    (run replay.tape
      (prefixMiddleScript firstWork secondWork z replay.body initialDigest)
      replay.oracle).2
    replay.record replay.finalDigest suffixSuccess
  obtain ⟨candidateRun, _candidateOracle, event⟩ :=
    successful_alpha_boundary staged.out staged.gamma replay.body z prefixDigest
      replay.tape
      (run replay.tape
        (sourceThenGammaScript firstWork secondWork replay.body initialDigest)
        replay.oracle).2
      staged.middle middleDigest middleSuccess
  have alphaEq : staged.middle.middle.alpha0 =
      replay.record.middle.middle.alpha0 := by
    have h := congrArg
      (fun r : Record replay.body z => r.middle.middle.alpha0) recordEq
    simpa using h.symm
  exact ⟨staged, prefixDigest, middleDigest, recordEq, sourceSuccess,
    middleSuccess, candidateRun, alphaEq, event⟩

/-- The literal pre-alpha transcript is itself produced by replay success;
later fork code need not accept it as an independent input. -/
theorem successful_replay_constructs_actual_alpha_boundary
    {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork) :
    ∃ afterAlphaNonce, IsActualAlphaBoundary replay afterAlphaNonce := by
  have actual := successful_replay_constructs_actual_alpha_run replay
  unfold ActualAlphaRun at actual
  rcases actual with ⟨staged, prefixDigest, middleDigest, recordEq,
    sourceSuccess, middleSuccess, _candidateSuccess, _alphaEq, _event⟩
  let sourceState :=
    (run replay.tape
      (sourceThenGammaScript firstWork secondWork replay.body initialDigest)
      replay.oracle).2
  let afterAlphaNonce := alphaBoundary staged.out staged.gamma replay.body z
    prefixDigest replay.tape sourceState staged.middle
  refine ⟨afterAlphaNonce, ?_⟩
  unfold IsActualAlphaBoundary
  exact ⟨staged, prefixDigest, middleDigest, recordEq, sourceSuccess,
    middleSuccess, rfl⟩

#print axioms successful_replay_constructs_actual_alpha_run
#print axioms successful_replay_constructs_actual_alpha_boundary

end
end AspisV8Completion.SuccessfulReplayAlphaBoundary
