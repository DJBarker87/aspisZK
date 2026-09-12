import FSLiveAlphaBoundary

/-!
# Pre-alpha response equality or a concrete full-output collision

Four alpha continuations cannot be made response-compatible merely because
their parsed response fields happen to be equal.  This leaf proves the
source-shaped alternative needed by the collector: if two executions reach
the same literal alpha candidate input but used different response0 bytes,
then one of the two actual absorb calls exhibits distinct inputs with the
same full 256-bit output.

The collision witness is local to the two executions.  A later scheduler
theorem must prove that both calls are represented in one global random-oracle
experiment before assigning it probability.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.FSV8AlphaResponseCollisionDichotomy

open FSOracleExecution FSBoundedTranscript
open FSV8AlphaChallengeInputBridge
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSLiveSelectedMiddleQueryRho SameBodyFunctionalProducerSource

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Transcript := FSBoundedTranscript.Transcript

def absorbInput (before : Transcript) (label : UInt8) (data : Bytes) : Bytes :=
  List.ofFn before.digest ++ [0, label] ++ data

def FullOutputCollision
    (leftInput rightInput : Bytes) (leftOutput rightOutput : Block) : Prop :=
  leftInput ≠ rightInput ∧ leftOutput = rightOutput

private theorem block_bytes_injective (left right : Block)
    (same : (List.ofFn left : List UInt8) = List.ofFn right) :
    left = right :=
  List.ofFn_injective same

theorem absorb_digest (tape : Tape) (before : Transcript)
    (label : UInt8) (data : Bytes) :
    (absorb tape before label data).digest =
      (query tape before.oracle (absorbInput before label data)).1 := by
  rfl

private theorem absorb_input_data_injective
    (left right : Transcript) (label : UInt8) (leftData rightData : Bytes)
    (same : absorbInput left label leftData =
      absorbInput right label rightData) :
    leftData = rightData := by
  have tail := congrArg (List.drop 34) same
  simpa [absorbInput] using tail

private theorem absorb_input_digest_injective
    (left right : Transcript) (label : UInt8) (leftData rightData : Bytes)
    (same : absorbInput left label leftData =
      absorbInput right label rightData) :
    left.digest = right.digest := by
  apply block_bytes_injective
  have headEq := congrArg (List.take 32) same
  simpa [absorbInput] using headEq

private theorem alpha_candidate_input_digest_injective
    (left right : Transcript)
    (same : alphaCandidateInput left = alphaCandidateInput right) :
    left.digest = right.digest := by
  apply block_bytes_injective
  have headEq := congrArg (List.take 32) same
  simpa [alphaCandidateInput] using headEq

/-- Two actual response0/alpha-nonce absorb chains which lead to the same
literal alpha candidate input either used identical response0 bytes or expose
a full-output collision at the response0 absorb or the following nonce
absorb.  No hash injectivity assumption is used. -/
theorem response0_eq_or_full_output_collision
    (leftTape rightTape : Tape)
    (leftBefore rightBefore : Transcript)
    (leftResponse rightResponse leftNonce rightNonce : Bytes)
    (sameCandidate :
      alphaCandidateInput
          (absorb leftTape
            (absorb leftTape leftBefore 52 leftResponse) 20 leftNonce) =
        alphaCandidateInput
          (absorb rightTape
            (absorb rightTape rightBefore 52 rightResponse) 20 rightNonce)) :
    leftResponse = rightResponse ∨
      FullOutputCollision
        (absorbInput leftBefore 52 leftResponse)
        (absorbInput rightBefore 52 rightResponse)
        (absorb leftTape leftBefore 52 leftResponse).digest
        (absorb rightTape rightBefore 52 rightResponse).digest ∨
      FullOutputCollision
        (absorbInput (absorb leftTape leftBefore 52 leftResponse) 20 leftNonce)
        (absorbInput (absorb rightTape rightBefore 52 rightResponse) 20 rightNonce)
        (absorb leftTape
          (absorb leftTape leftBefore 52 leftResponse) 20 leftNonce).digest
        (absorb rightTape
          (absorb rightTape rightBefore 52 rightResponse) 20 rightNonce).digest := by
  by_cases responseEq : leftResponse = rightResponse
  · exact Or.inl responseEq
  · right
    have firstInputNe :
        absorbInput leftBefore 52 leftResponse ≠
          absorbInput rightBefore 52 rightResponse := by
      intro inputEq
      exact responseEq
        (absorb_input_data_injective leftBefore rightBefore 52
          leftResponse rightResponse inputEq)
    let leftAfterResponse := absorb leftTape leftBefore 52 leftResponse
    let rightAfterResponse := absorb rightTape rightBefore 52 rightResponse
    by_cases firstOutputEq :
        leftAfterResponse.digest = rightAfterResponse.digest
    · exact Or.inl ⟨firstInputNe, firstOutputEq⟩
    · right
      have secondInputNe :
          absorbInput leftAfterResponse 20 leftNonce ≠
            absorbInput rightAfterResponse 20 rightNonce := by
        intro inputEq
        exact firstOutputEq
          (absorb_input_digest_injective leftAfterResponse rightAfterResponse
            20 leftNonce rightNonce inputEq)
      have finalOutputEq :
          (absorb leftTape leftAfterResponse 20 leftNonce).digest =
            (absorb rightTape rightAfterResponse 20 rightNonce).digest :=
        alpha_candidate_input_digest_injective _ _ sameCandidate
      exact ⟨secondInputNe, finalOutputEq⟩

def beforeResponse0
    (out : FSV7OODBodyScript.Result) (gamma : FSNonzeroQM31.K)
    (body : Bytes) (z : Fin 10 → FSNonzeroQM31.K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (success : Success out gamma body z) : Transcript :=
  let afterInactive := absorb tape ⟨digest, oracle⟩ 50
    (inactiveClaimBytes body)
  let kappaDraw := FSNonzeroQM31.nonzero tape 3 afterInactive
  let afterDescription :=
    absorb tape kappaDraw.2 1 success.functional.description
  let afterClaim := absorb tape afterDescription 6 success.functional.claim
  let afterImageProfile :=
    absorb tape afterClaim 1 compactFunctionalProfile
  (FSNonzeroQM31.nonzero tape 3 afterImageProfile).2

theorem alphaBoundary_is_two_absorbs
    (out : FSV7OODBodyScript.Result) (gamma : FSNonzeroQM31.K)
    (body : Bytes) (z : Fin 10 → FSNonzeroQM31.K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (success : Success out gamma body z) :
    FSLiveAlphaBoundary.alphaBoundary out gamma body z digest tape oracle
        success =
      absorb tape
        (absorb tape
          (beforeResponse0 out gamma body z digest tape oracle success)
          52 (0 :: response0Bytes body))
        20 (0 :: alpha0NonceBytes body) := by
  rfl

/-- Actual V8 specialization.  Equality of the literal alpha query inputs
forces equality of the six canonical response0 field encodings unless one of
the two real transcript absorbs exposes a full-output collision. -/
theorem live_response0_eq_or_full_output_collision
    (leftOut rightOut : FSV7OODBodyScript.Result)
    (leftGamma rightGamma : FSNonzeroQM31.K)
    (leftBody rightBody : Bytes)
    (leftZ rightZ : Fin 10 → FSNonzeroQM31.K)
    (leftDigest rightDigest : Block)
    (leftTape rightTape : Tape) (leftOracle rightOracle : Oracle)
    (leftSuccess : Success leftOut leftGamma leftBody leftZ)
    (rightSuccess : Success rightOut rightGamma rightBody rightZ)
    (sameCandidate :
      alphaCandidateInput
          (FSLiveAlphaBoundary.alphaBoundary leftOut leftGamma leftBody leftZ
            leftDigest leftTape leftOracle leftSuccess) =
        alphaCandidateInput
          (FSLiveAlphaBoundary.alphaBoundary rightOut rightGamma rightBody
            rightZ rightDigest rightTape rightOracle rightSuccess)) :
    response0Bytes leftBody = response0Bytes rightBody ∨
      FullOutputCollision
        (absorbInput
          (beforeResponse0 leftOut leftGamma leftBody leftZ leftDigest leftTape
            leftOracle leftSuccess)
          52 (0 :: response0Bytes leftBody))
        (absorbInput
          (beforeResponse0 rightOut rightGamma rightBody rightZ rightDigest
            rightTape rightOracle rightSuccess)
          52 (0 :: response0Bytes rightBody))
        (absorb leftTape
          (beforeResponse0 leftOut leftGamma leftBody leftZ leftDigest leftTape
            leftOracle leftSuccess)
          52 (0 :: response0Bytes leftBody)).digest
        (absorb rightTape
          (beforeResponse0 rightOut rightGamma rightBody rightZ rightDigest
            rightTape rightOracle rightSuccess)
          52 (0 :: response0Bytes rightBody)).digest ∨
      FullOutputCollision
        (absorbInput
          (absorb leftTape
            (beforeResponse0 leftOut leftGamma leftBody leftZ leftDigest
              leftTape leftOracle leftSuccess)
            52 (0 :: response0Bytes leftBody))
          20 (0 :: alpha0NonceBytes leftBody))
        (absorbInput
          (absorb rightTape
            (beforeResponse0 rightOut rightGamma rightBody rightZ rightDigest
              rightTape rightOracle rightSuccess)
            52 (0 :: response0Bytes rightBody))
          20 (0 :: alpha0NonceBytes rightBody))
        (FSLiveAlphaBoundary.alphaBoundary leftOut leftGamma leftBody leftZ
          leftDigest leftTape leftOracle leftSuccess).digest
        (FSLiveAlphaBoundary.alphaBoundary rightOut rightGamma rightBody rightZ
          rightDigest rightTape rightOracle rightSuccess).digest := by
  have classified := response0_eq_or_full_output_collision
    leftTape rightTape
    (beforeResponse0 leftOut leftGamma leftBody leftZ leftDigest leftTape
      leftOracle leftSuccess)
    (beforeResponse0 rightOut rightGamma rightBody rightZ rightDigest rightTape
      rightOracle rightSuccess)
    (0 :: response0Bytes leftBody) (0 :: response0Bytes rightBody)
    (0 :: alpha0NonceBytes leftBody) (0 :: alpha0NonceBytes rightBody)
    (by simpa [alphaBoundary_is_two_absorbs] using sameCandidate)
  rcases classified with responseEq | collision
  · exact Or.inl (List.cons.inj responseEq).2
  · exact Or.inr collision

#print axioms response0_eq_or_full_output_collision
#print axioms live_response0_eq_or_full_output_collision

end AspisV8Completion.FSV8AlphaResponseCollisionDichotomy
