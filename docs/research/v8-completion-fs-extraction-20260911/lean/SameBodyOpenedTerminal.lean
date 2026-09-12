import SameBodyOpenedCovector
import SameBodyTerminalExecution

/-! DRAFT: conditional byte/causal-tail join with explicit missing producer.
`EncodedCausalFields` is an UNPROVED source-execution obligation, not an
acceptance definition: every actual canonical body field must be the field
serialized by one legal strategy on the realised continuation. It does not
construct that strategy or claim chronological/ROM coupling. Below, parsing
constructs the unique word equality, then the actual response0 scalar,
positive query update and terminal comparison use that SAME parsed word.
Ordinary scalar, initial covector, Data and revealed coins remain source
boundaries. No arbitrary final, opened values or terminal equality is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
namespace AspisV8.SameBodyOpenedTerminal
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCQM31Representation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.SameBodyAuthenticatedSlots AspisV8.SameBodyOpenedRun
open AspisV8.SameBodyOpenedQueryUpdate AspisV8.SameBodyOpenedCovector
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional
open AspisV8.OptimizedRelationRefinement
open AspisV8Completion.SameBodyRelation AspisV8Completion.SameBodyQueryClaimExact
open AspisV8Completion.SameBodyTerminalExecution
open scoped BigOperators
noncomputable section
abbrev K := QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def wordFrom (result : Output) : Word K := fun i => result.wire.values.getD i.val 0

theorem wordFrom_final (result : Output) : finalValues (wordFrom result) = finalFromWire result := rfl

/-- Exact missing source-serialization obligation. In particular it is not
deduced merely from root agreement or a supplied hash-answer log. -/
def EncodedCausalFields (body : List Byte) (early : Fin 417 → K)
    (strategy : Strategy K (Fin 22 → Position)) (tau alpha rho : K)
    (query : Fin 22 → Position) (coins : Fin 3 → K) : Prop :=
  ∀ i : Fin 697, decodeQM31ExactLE (CanonicalRelationInput.fieldBytes body i) =
    some (produce early strategy tau alpha query rho coins i)

theorem parsed_word_of_encoded_fields (view : RawHashInput → Digest208)
    (body : List Byte) (query : Fin 22 → Position) (d : Data (K := K))
    (result : Output) (success : run view body query d = some result)
    (early : Fin 417 → K) (strategy : Strategy K (Fin 22 → Position))
    (tau alpha rho : K) (coins : Fin 3 → K)
    (encoded : EncodedCausalFields body early strategy tau alpha rho query coins) :
    wordFrom result = produce early strategy tau alpha query rho coins := by
  funext i
  have parsed := (SelectedWireBytes.fixed_fields body result.wire
    (run_checks view body query d result success).1).2 i
  exact Option.some.inj (parsed.symm.trans (encoded i))

def priorFrom (result : Output) (ordinary alpha : K) : K :=
  (ringArithmetic (1/4 : K)).evaluate7
    (compact (ringArithmetic (1/4 : K)).toArithmetic ordinary
      (response (wordFrom result) 0)) alpha

/-- Actual same-word scalar/update and terminal check. The weight argument
is the already first-folded ordinary/image weight, not a supplied terminal. -/
def checkOpened (result : Output) (d : Data (K := K)) (query : Fin 22 → Position)
    (alpha ordinary rho : K) (coins : Fin 3 → K) (weight : Fin 256 → K) : Bool :=
  check (1/4 : K) (wordFrom result) (updatedWeights weight query rho)
    (positiveUpdate result d query alpha (priorFrom result ordinary alpha) rho) coins

attribute [local irreducible] wordFrom priorFrom updatedWeights positiveUpdate

theorem successful_check_constructs_terminal_zero
    (view : RawHashInput → Digest208) (body : List Byte)
    (query : Fin 22 → Position) (d : Data (K := K)) (result : Output)
    (success : run view body query d = some result)
    (early : Fin 417 → K) (strategy : Strategy K (Fin 22 → Position))
    (tau alpha ordinary rho : K) (coins : Fin 3 → K) (weight : Fin 256 → K)
    (encoded : EncodedCausalFields body early strategy tau alpha rho query coins)
    (hq : (1/4 : K)*4 = 1)
    (accepted : checkOpened result d query alpha ordinary rho coins weight = true) :
    terminalZero
      ((typedTail (((strategy tau).afterAlpha0 alpha).afterQueries query rho)).raw.toGame
        (1/4 : K) hq (updatedWeights weight query rho)
        ((strategy tau).afterAlpha0 alpha).final256
        (positiveUpdate result d query alpha (priorFrom result ordinary alpha) rho))
      [coins 0, coins 1, coins 2] := by
  have same := parsed_word_of_encoded_fields view body query d result success
    early strategy tau alpha rho coins encoded
  unfold checkOpened at accepted
  rw [same] at accepted
  let initial := positiveUpdate result d query alpha (priorFrom result ordinary alpha) rho
  let newWeight := updatedWeights weight query rho
  change check (1/4 : K) (produce early strategy tau alpha query rho coins)
    newWeight initial coins = true at accepted
  change terminalZero
    ((typedTail (((strategy tau).afterAlpha0 alpha).afterQueries query rho)).raw.toGame
      (1/4 : K) hq newWeight ((strategy tau).afterAlpha0 alpha).final256 initial)
    [coins 0, coins 1, coins 2]
  have terminal := produced_check_constructs_terminal_zero
    (K := K) (Schedule := Fin 22 → Position)
    (quarter := (1/4 : K))
    (initial := initial)
    (hq := hq) (early := early) (strategy := strategy) (tau := tau)
    (alpha0 := alpha) (rho := rho) (queries := query) (coins := coins)
    (weight := newWeight) (success := accepted)
  exact terminal

/-- The incoming game discrepancy is computed by the source response0 and
positive update, and related to the authenticated fixed-prefix quotient.
This does not assert that the arbitrary incoming ordinary/image weight is
the correct source-produced functional; that producer remains separate. -/
theorem computed_incoming_discrepancy_or_failure
    (view : RawHashInput → Digest208) (body : List Byte)
    (query : Fin 22 → Position) (d : Data (K := K)) (result : Output)
    (success : run view body query d = some result)
    (c1Prefix c2Prefix : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1Prefix, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1Prefix) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog
      (MinimalMultiproofPaths.leafLog query (wireRecords result.wire) ++ result.trace) fullLog)
    (alpha ordinary rho : K) (weight : Fin 256 → K) :
    AuthenticationFailure view c1Prefix c2Prefix (wireRoots result.wire) fullLog query ∨
      positiveUpdate result d query alpha (priorFrom result ordinary alpha) rho -
        (∑ i : Fin 256, finalValues (wordFrom result) i * updatedWeights weight query rho i) =
      (priorFrom result ordinary alpha -
        ∑ i : Fin 256, finalValues (wordFrom result) i*weight i) -
        rho*∑ j : Fin 22, PostQueryFunctional.residual (finalValues (wordFrom result))
          (fun k => storedPoint (K := K) (query k))
          (fixedReceived result d c1Prefix c2Prefix alpha) j * rho^j.val := by
  have incoming := successful_opened_covector_or_failure
    (view := view) (body := body) (query := query) (d := d) (result := result)
    (success := success) (c1Prefix := c1Prefix) (c2Prefix := c2Prefix)
    (fullLog := fullLog) (c1Answers := c1Answers) (c2Answers := c2Answers)
    (c1Included := c1Included) (c2Included := c2Included) (callsIncluded := callsIncluded)
    (alpha := alpha) (prior := priorFrom result ordinary alpha) (rho := rho) (weight := weight)
  let statement (final : Fin 256 → K) : Prop :=
    AuthenticationFailure view c1Prefix c2Prefix (wireRoots result.wire) fullLog query ∨
      positiveUpdate result d query alpha (priorFrom result ordinary alpha) rho -
        (∑ i : Fin 256, final i * updatedWeights weight query rho i) =
      (priorFrom result ordinary alpha - ∑ i : Fin 256, final i*weight i) -
        rho*∑ j : Fin 22, PostQueryFunctional.residual final
          (fun k => storedPoint (K := K) (query k))
          (fixedReceived result d c1Prefix c2Prefix alpha) j * rho^j.val
  have replacement : statement (finalValues (wordFrom result)) =
      statement (finalFromWire result) := congrArg statement (wordFrom_final result)
  exact Eq.mpr replacement incoming

#print successful_check_constructs_terminal_zero
#print axioms parsed_word_of_encoded_fields
#print axioms successful_check_constructs_terminal_zero
#print axioms computed_incoming_discrepancy_or_failure
end
end AspisV8.SameBodyOpenedTerminal
