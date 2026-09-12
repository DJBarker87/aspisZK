import SameBodyFunctionalProducerSource

/-!
# Fallible source-driven selected middle transcript

This is the source-shaped replacement for the total `FunctionalProducer`
boundary.  Immediately after kappa it executes `fromInputs`; failure is an
explicit terminal result and consumes no description/profile hash call.
Success absorbs the constructed 545-byte description and 16-byte claim, then
uses the unchanged image-profile/tau/response0/alpha0/query/rho order.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSLiveSourceFunctionalMiddle

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31 FSLiveNonzeroV7Decode
open FSLiveQueryRhoSuffix FSLiveSelectedMiddleQueryRho
open SameBodyFunctionalProducerSource

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result
abbrev MiddleSuccess := FSLiveSelectedMiddleQueryRho.Success

noncomputable section

inductive Error where
  | kappa (error : FSNonzeroQM31.Error)
  | functional
  | tau (error : FSNonzeroQM31.Error)
  | alpha0 (error : FSNonzeroQM31.Error)
  | suffix (error : FSLiveQueryRhoSuffix.Error)
  deriving DecidableEq

structure Success (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) where
  middle : MiddleSuccess
  functional : Encoded
  functionalRun :
    fromInputs out gamma middle.kappa body z = some functional

abbrev Result (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) := Except Error (Success out gamma body z)

/-- Exact continuation after a successful source construction. -/
def afterFunctionalScript (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (kappa : K) (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : Block) :=
  FSTranscriptScript.bind (absorbScript digest 1 functional.description) fun afterDescription =>
    FSTranscriptScript.bind (absorbScript afterDescription 6 functional.claim) fun afterClaim =>
      FSTranscriptScript.bind (absorbScript afterClaim 1 compactFunctionalProfile)
          fun afterImageProfile =>
        FSTranscriptScript.bind (nonzeroScript 3 afterImageProfile) fun tauDraw =>
          match tauDraw.1 with
          | .error e => .done
              (Except.error (Error.tau e), tauDraw.2)
          | .ok tau =>
            FSTranscriptScript.bind (absorbScript tauDraw.2 52 (0 :: response0Bytes body))
                fun afterResponse0 =>
              FSTranscriptScript.bind (absorbScript afterResponse0 20
                  (0 :: alpha0NonceBytes body)) fun afterAlphaNonce =>
                FSTranscriptScript.bind (candidateScript afterAlphaNonce) fun alphaDraw =>
                  match alphaDraw.1 with
                  | .error e => .done
                      (Except.error (Error.alpha0 e), alphaDraw.2)
                  | .ok alpha0 =>
                    FSTranscriptScript.bind (m := 0) (queryRhoScript body alphaDraw.2)
                      fun suffixDraw =>
                        .done (match suffixDraw.1 with
                          | .error e =>
                            (Except.error (Error.suffix e), suffixDraw.2)
                          | .ok (queries, rho) =>
                            let middle := FSLiveSelectedMiddleQueryRho.Success.mk
                              kappa tau alpha0 queries rho
                            let sourceSuccess : Success out gamma body z :=
                              { middle := middle
                                functional := functional
                                functionalRun := functionalRun }
                            (Except.ok
                              sourceSuccess, suffixDraw.2))

/-- Fallible selected middle.  The public point `z` remains explicit until its
statement/context producer is connected. -/
def middleScript (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) :=
  FSTranscriptScript.bind (absorbScript digest 50 (inactiveClaimBytes body)) fun afterInactive =>
    FSTranscriptScript.bind (nonzeroScript 3 afterInactive) fun kappaDraw =>
      match kappaDraw.1 with
      | .error e => .done (Except.error (Error.kappa e), kappaDraw.2)
      | .ok kappa =>
        match functionalRun : fromInputs out gamma kappa body z with
        | none => .done (Except.error Error.functional, kappaDraw.2)
        | some functional =>
          afterFunctionalScript out gamma body z kappa functional functionalRun
            kappaDraw.2

theorem successful_run_provenance (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) (tape : Tape) (oracle : Oracle)
    (success : Success out gamma body z) (finalDigest : Block)
    (accepted :
      (run tape (middleScript out gamma body z digest) oracle).1 =
        some (Except.ok success, finalDigest)) :
    fromInputs out gamma success.middle.kappa body z = some success.functional ∧
      success.functional.description.length = 545 ∧
      success.functional.claim.length = 16 ∧
      success.functional.data.Checked ∧
      success.functional.data.gamma = gamma := by
  have runEq := success.functionalRun
  exact ⟨runEq,
    (fromInputs_lengths _ _ _ _ _ _ runEq).1,
    (fromInputs_lengths _ _ _ _ _ _ runEq).2,
    fromInputs_data_checked _ _ _ _ _ _ runEq,
    fromInputs_data_gamma _ _ _ _ _ _ runEq⟩

/-- The source-driven success exposes exactly the existing selected-middle
result record; no challenge/result field is renamed or defaulted. -/
theorem successful_middle_shape (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (success : Success out gamma body z) :
    success.middle =
      FSLiveSelectedMiddleQueryRho.Success.mk success.middle.kappa success.middle.tau
        success.middle.alpha0 success.middle.queries success.middle.rho := by
  cases success.middle
  rfl

#print axioms successful_run_provenance
#print axioms successful_middle_shape

end
end AspisV8Completion.FSLiveSourceFunctionalMiddle
