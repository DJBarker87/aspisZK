import FSBoundedTranscript
import AspisFormal.K1.V7FsAokExperiment
import AspisFormal.K1.V7Tag73AdaptiveLazyOracle

/-!
# Separation of the alpha marker and first candidate inputs

The marker absorb uses a longer, tagged input than the first squeeze of the
post-marker candidate.  This leaf also records the elementary lazy-oracle
fact that a successful query at a different input cannot change a target
lookup.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8AlphaMarkerCandidateSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open FSBoundedTranscript

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

/-- The literal alpha-marker absorb input cannot be the first candidate
    squeeze input, independently of either digest or payload. -/
theorem alpha_marker_absorb_input_ne_candidate_input
    (beforeDigest candidateDigest : Block) (payload : Bytes) :
    List.ofFn beforeDigest ++ [0, 20] ++ (0 :: payload) ≠
      List.ofFn candidateDigest ++ [1] := by
  intro equal
  have lengths := congrArg List.length equal
  simp only [List.length_append, List.length_ofFn, List.length_cons] at lengths
  omega

/-- A successful oracle call changes the table only at its queried input.
    Thus every lookup at a distinct target is unchanged. -/
theorem queryOracle_success_preserves_lookup_of_ne
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input target : ShaInput) (output : ShaOutput)
    (inputNeTarget : input ≠ target)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    lookupEntry nextState target = lookupEntry state target := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      rfl
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          unfold lookupEntry
          rw [List.find?_append]
          cases selected : state.table.find? (fun entry => entry.input = target) with
          | some entry => simp [selected]
          | none => simp [selected, inputNeTarget]

#print axioms alpha_marker_absorb_input_ne_candidate_input
#print axioms queryOracle_success_preserves_lookup_of_ne

end AspisV8Completion.FSV8AlphaMarkerCandidateSeparation
