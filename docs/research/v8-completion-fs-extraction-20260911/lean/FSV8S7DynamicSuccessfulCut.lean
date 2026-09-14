import FSV8S7DynamicSelectedRoot

/-!
# Successful dynamic source cut

A successful result of the guard-relaxed dynamic verifier determines the
post-semantic oracle and the exact same-body suffix invocation.  Neither the
semantic state, parsed wire, oracle cut nor suffix equality is supplied by the
caller.

This is the concrete cut consumed by later authentication chronology.  Its
`operationalCuts` contain only the roots read by the functional Merkle check;
it does not claim that their inert analysis fields are chronological C1/C2
cuts, and it does not add the omitted semantic terminal guard.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8S7DynamicSuccessfulCut

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSLiveSemanticPrefix SameBodySemanticWire
open FSV8S4VerifierOnlySuffix
open FSV8S7DynamicSelectedRoot

noncomputable section

abbrev Bytes := List UInt8
abbrev B := FSBoundedTranscript.Block

/-- Exact decomposition of a successful dynamically indexed verifier run.
The existential oracle states are outputs of the two actual executions. -/
theorem successful_verifier_constructs_post_semantic_cut
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (initial : Oracle)
    (accepted : AspisV8Completion.FSV8S7DynamicSelectedRoot.RelaxedSuccess body)
    (digest : B)
    (success :
      (run tape (verifierScript positiveTransfer binding body) initial).1 =
        some (.ok accepted, digest)) :
    ∃ wire postSemantic postSuffix,
      SameBodySemanticWire.parse body = some wire ∧
      run tape (semanticScript positiveTransfer binding body) initial =
        (some (.ok accepted.semantic), postSemantic) ∧
      run tape
          (selectedSuffixBeforePoints accepted.semantic.z
            (operationalCuts wire) body accepted.semantic.finalDigest)
          postSemantic =
        (some (.ok accepted.record, digest), postSuffix) ∧
      (run tape (verifierScript positiveTransfer binding body) initial).2 =
        postSuffix ∧
      accepted.finalDigest = digest := by
  unfold verifierScript at success
  rw [run_bind] at success
  cases semanticExecution :
      run tape (semanticScript positiveTransfer binding body) initial with
  | mk semanticResult postSemantic =>
    cases semanticResult with
    | none => simp [semanticExecution] at success
    | some semantic =>
      cases semantic with
      | error error => simp [semanticExecution, FSOracleExecution.run] at success
      | ok state =>
        cases parsed : SameBodySemanticWire.parse body with
        | none =>
          simp [semanticExecution, cutsFromBody, parsed, FSOracleExecution.run]
            at success
        | some wire =>
          simp only [semanticExecution, cutsFromBody, parsed, Option.map_some]
            at success
          rw [run_map] at success
          cases suffixExecution :
              run tape
                (selectedSuffixBeforePoints state.z (operationalCuts wire) body
                  state.finalDigest)
                postSemantic with
          | mk suffixResult postSuffix =>
            cases suffixResult with
            | none => simp [suffixExecution] at success
            | some suffix =>
              rcases suffix with ⟨result, finalDigest⟩
              cases result with
              | error error => simp [suffixExecution] at success
              | ok record =>
                simp [suffixExecution] at success
                rcases success with ⟨rfl, rfl⟩
                refine ⟨wire, postSemantic, postSuffix, rfl, ?_, ?_, ?_, rfl⟩
                · rfl
                · exact suffixExecution
                · simp [verifierScript, semanticExecution, cutsFromBody, parsed,
                    run_bind, run_map, suffixExecution]

#print axioms successful_verifier_constructs_post_semantic_cut

end
end AspisV8Completion.FSV8S7DynamicSuccessfulCut
