import FSLiveLaterRelationSuffix
import FSV7PrefixBridge
import SameBodySequentialCodec
import SameBodyRelation

/-!
# Canonical same-body terminal input from live relation coins

This leaf constructs the terminal relation *input* from one literal body and
one successful chronological suffix.  The 697-field word is produced by the
source-shaped sequential canonical decoder.  The three later coins are
projections of the live alpha1--alpha3 results, never caller-supplied values.

The authenticated query-increment arithmetic remains an explicit producer.
No `SameBodyRelation.consume` success, terminal-zero equation, payment
acceptance, freshness or probability statement is assumed or concluded.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.SameBodyLiveTerminalInput

open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisV8.CanonicalRelationInput
open AspisV8.SameBodySequentialCodec
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix
open SameBodyRelation

abbrev Bytes := List UInt8
abbrev WireBytes := List (Fin 256)
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

noncomputable section

/-- Data available at the terminal boundary.  `canonical` is constructed by
`fromBody`; it is not a coherence certificate supplied to the final theorem.
`incrementBytes` records exactly what was absorbed by the live suffix while
leaving its pinned Rust arithmetic producer as an explicit boundary. -/
structure Input where
  body : Bytes
  values : List K
  canonical : AspisV8.SameBodySequentialCodec.fields
    (FSV7PrefixBridge.encode body) = some values
  ood : OODResult
  gamma : K
  middle : FSLiveSelectedMiddleQueryRho.Success
  later : FSLiveLaterRelationSuffix.Success
  incrementBytes : Bytes

def Input.word (input : Input) : Word K :=
  fun i => input.values.getD i.val 0

def Input.response0 (input : Input) : Sent K := response input.word 0
def Input.final256 (input : Input) : Final K := finalValues input.word
def Input.laterResponses (input : Input) : List (Sent K) :=
  SameBodyRelation.laterResponses input.word
def Input.coins (input : Input) : Fin 3 -> K := input.later.coins

/-- Parse once from the literal body.  Failure, including any noncanonical
limb or invalid body length, returns `none`; no default word is constructed. -/
def fromBody (producer : IncrementProducer) (ood : OODResult) (gamma : K)
    (middle : FSLiveSelectedMiddleQueryRho.Success)
    (later : FSLiveLaterRelationSuffix.Success) (body : Bytes) : Option Input :=
  match h : AspisV8.SameBodySequentialCodec.fields
      (FSV7PrefixBridge.encode body) with
  | none => none
  | some values => some {
      body := body
      values := values
      canonical := h
      ood := ood
      gamma := gamma
      middle := middle
      later := later
      incrementBytes := producer.bytes ood gamma middle body }

theorem fromBody_constructs_canonical
    (producer : IncrementProducer) (ood : OODResult) (gamma : K)
    (middle : FSLiveSelectedMiddleQueryRho.Success)
    (later : FSLiveLaterRelationSuffix.Success) (body : Bytes) (input : Input)
    (success : fromBody producer ood gamma middle later body = some input) :
    input.body = body /\
    AspisV8.SameBodySequentialCodec.fields
      (FSV7PrefixBridge.encode input.body) = some input.values /\
    input.ood = ood /\ input.gamma = gamma /\ input.middle = middle /\
    input.later = later /\
    input.incrementBytes = producer.bytes ood gamma middle body := by
  unfold fromBody at success
  split at success
  · contradiction
  next values h =>
    have same := Option.some.inj success
    subst input
    exact ⟨rfl, h, rfl, rfl, rfl, rfl, rfl⟩

/-- Every compact response value in the terminal record is the canonical
decode of its exact fixed-field bytes in the same body. -/
theorem canonical_response_field (input : Input) (round : Fin 4)
    (sent : Fin 6) :
    decodeQM31ExactLE
        (AspisV8.CanonicalRelationInput.fieldBytes
          (FSV7PrefixBridge.encode input.body)
          (AspisV8.CanonicalRelationInput.relationIndex round sent)) =
      some (response input.word round sent) := by
  have parsed : AspisV8.CanonicalRelationInput.parseFixed
      (FSV7PrefixBridge.encode input.body) = some input.values := by
    rw [<- AspisV8.SameBodySequentialCodec.fields_eq_parseFixed]
    exact input.canonical
  have decoded := AspisV8.CanonicalRelationInput.decoded_response
    (FSV7PrefixBridge.encode input.body) input.values parsed round sent
  simpa [Input.word, SameBodyRelation.response, SameBodyRelation.responseIndex,
    AspisV8.CanonicalRelationInput.response_sent] using decoded

/-- Every final coefficient is likewise derived from the canonical fixed
section of the same body; no separately supplied final vector occurs. -/
theorem canonical_final_field (input : Input) (coefficient : Fin 256) :
    decodeQM31ExactLE
        (AspisV8.CanonicalRelationInput.fieldBytes
          (FSV7PrefixBridge.encode input.body)
          (AspisV8.CanonicalRelationInput.finalIndex coefficient)) =
      some (input.final256 coefficient) := by
  have parsed : AspisV8.CanonicalRelationInput.parseFixed
      (FSV7PrefixBridge.encode input.body) = some input.values := by
    rw [<- AspisV8.SameBodySequentialCodec.fields_eq_parseFixed]
    exact input.canonical
  have decoded := AspisV8.CanonicalRelationInput.decoded_final
    (FSV7PrefixBridge.encode input.body) input.values parsed coefficient
  simpa [Input.final256, Input.word, SameBodyRelation.finalValues,
    SameBodyRelation.finalIndex] using decoded

/-- The terminal coins are exactly the chronological alpha results. -/
theorem live_coins_literal (input : Input) :
    input.coins 0 = input.later.alpha1 /\
    input.coins 1 = input.later.alpha2 /\
    input.coins 2 = input.later.alpha3 :=
  input.later.coins_literal

/-- This equality identifies, without validating, the explicit arithmetic
producer whose bytes the suffix absorbed before response1. -/
theorem increment_bytes_literal
    (producer : IncrementProducer) (ood : OODResult) (gamma : K)
    (middle : FSLiveSelectedMiddleQueryRho.Success)
    (later : FSLiveLaterRelationSuffix.Success) (body : Bytes) (input : Input)
    (success : fromBody producer ood gamma middle later body = some input) :
    input.incrementBytes = producer.bytes input.ood input.gamma input.middle input.body := by
  have facts := fromBody_constructs_canonical
    producer ood gamma middle later body input success
  calc
    input.incrementBytes = producer.bytes ood gamma middle body := facts.2.2.2.2.2.2
    _ = producer.bytes input.ood input.gamma input.middle input.body := by
      rw [facts.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.1]

#print axioms fromBody_constructs_canonical
#print axioms canonical_response_field
#print axioms canonical_final_field
#print axioms live_coins_literal
#print axioms increment_bytes_literal

end
end AspisV8Completion.SameBodyLiveTerminalInput
