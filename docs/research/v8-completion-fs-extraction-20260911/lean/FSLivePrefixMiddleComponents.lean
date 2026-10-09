import FSAuthenticatedInterleavedPrefixMiddle

/-!
# Successful prefix-middle execution exposes its exact two source stages

This source-shaped elimination theorem connects a successful combined
source/OOD/gamma/middle execution to the literal successful middle run whose
alpha boundary is used by the fork analysis.  No replay, acceptance,
freshness, or probability premise is introduced.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSLivePrefixMiddleComponents

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSQuerySchedule
open FSInterleavedSelectedIncrementBoundary

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

noncomputable section

/-- A successful `prefixMiddleScript` is exactly a successful
`sourceThenGammaScript` followed, in the resulting oracle state, by the
successful literal source-functional middle recorded in `staged`. -/
theorem successful_prefix_middle_components {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle)
    (staged : Partial body z) (middleDigest : Block)
    (success :
      (run tape (prefixMiddleScript firstWork secondWork z body digest)
        oracle).1 = some (.ok staged, middleDigest)) :
    ∃ prefixDigest,
      (run tape (sourceThenGammaScript firstWork secondWork body digest)
        oracle).1 = some (.ok (staged.out, staged.gamma), prefixDigest) ∧
      (run tape
        (middleScript staged.out staged.gamma body z prefixDigest)
        (run tape (sourceThenGammaScript firstWork secondWork body digest)
          oracle).2).1 = some (.ok staged.middle, middleDigest) := by
  unfold prefixMiddleScript at success
  rw [run_bind] at success
  cases prefixRun :
      (run tape (sourceThenGammaScript firstWork secondWork body digest)
        oracle).1 with
  | none => simp [prefixRun] at success
  | some prefixValue =>
      rcases prefixValue with ⟨prefixResult, prefixDigest⟩
      cases prefixResult with
      | error e => simp [prefixRun, run] at success
      | ok pair =>
          rcases pair with ⟨out, gamma⟩
          simp only [prefixRun] at success
          unfold middleContinuationAt at success
          rw [run_bind] at success
          cases middleRun :
              (run tape (middleScript out gamma body z prefixDigest)
                (run tape
                  (sourceThenGammaScript firstWork secondWork body digest)
                  oracle).2).1 with
          | none => simp [middleRun] at success
          | some middleValue =>
              rcases middleValue with ⟨middleResult, returnedDigest⟩
              cases middleResult with
              | error e => simp [middleRun, run] at success
              | ok middle =>
                  simp only [middleRun, run] at success
                  have same := Option.some.inj success
                  have recordEq := Except.ok.inj (congrArg Prod.fst same)
                  have digestEq := congrArg Prod.snd same
                  cases recordEq
                  have returnedDigestEq : returnedDigest = middleDigest := by
                    simpa using digestEq
                  refine ⟨prefixDigest, ?_, ?_⟩
                  · simpa using prefixRun
                  · simpa [returnedDigestEq] using middleRun

/-- A successful authenticated suffix retains the already-fixed
source/OOD/gamma/middle prefix of its returned record. -/
theorem successful_suffix_retains_partial
    (cuts : FSBoundedTranscript.RootCuts) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) (staged : Partial body z)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle)
    (record : Record body z) (finalDigest : Block)
    (success :
      (run tape (suffixContinuation cuts body z digest staged) oracle).1 =
        some (.ok record, finalDigest)) :
    record =
      { out := staged.out
        gamma := staged.gamma
        middle := staged.middle
        suffix := record.suffix } := by
  unfold suffixContinuation at success
  by_cases accepted : ValidAccepted staged.middle.middle.queries ∧
      staged.middle.middle.queries.length = 22
  · rw [dif_pos accepted, run_bind] at success
    cases suffixRun :
        (run tape
          (interleavedSelectedSuffix cuts
            (scheduleOf staged.middle.middle.queries accepted.1 accepted.2).positions
            body digest staged.middle.functional.data
            staged.middle.middle.alpha0 staged.middle.middle.rho)
          oracle).1 with
    | none => simp [suffixRun] at success
    | some suffixValue =>
        rcases suffixValue with ⟨suffixResult, suffixDigest⟩
        cases suffixResult with
        | error e => simp [suffixRun, run] at success
        | ok suffix =>
            simp only [suffixRun, run] at success
            have same := Option.some.inj success
            have recordEq := Except.ok.inj (congrArg Prod.fst same)
            cases recordEq
            rfl
  · rw [dif_neg accepted] at success
    simp [run] at success

#print axioms successful_prefix_middle_components
#print axioms successful_suffix_retains_partial

end
end AspisV8Completion.FSLivePrefixMiddleComponents
