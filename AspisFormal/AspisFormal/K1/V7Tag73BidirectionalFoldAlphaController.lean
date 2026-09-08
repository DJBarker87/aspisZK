import AspisFormal.K1.V7Tag73FoldArmedAlphaZeroController

/-!
# Bidirectional selected-fold/alpha causal controller

The deployed prover may query the selected fold-nonce boundary before it
queries the corresponding fold-work input.  A controller armed only at the
fold-work exposure therefore cannot use the already-consumed alpha answers as
fresh probability coordinates.

This controller is indexed instead by the first exposure of the selected
candidate pair.  The first input is parsed before its answer as either the
41-byte fold-work input or the corresponding 43-byte fold-nonce boundary.  It
then arms the missing sibling and the four-block alpha chain.  Consequently
the same five named coordinates are available in both chronological orders;
no answer or retrospective logical-role classifier is consulted to select the
anchor kind.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73BidirectionalFoldAlphaController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Recover the selected fold-work input from the exact fold-nonce absorption
input.  All three payload bytes, including the fixed zero suffix, are checked
before the inverse is returned. -/
def alphaBoundaryInputToFoldWork? (input : ShaInput) : Option ShaInput :=
  if input.length = 43 ∧ input[32]? = some domAbsorb ∧
      input[33]? = some foldWorkNonceLabel ∧ input[34]? = some 0 then
    some (input.take 32 ++ [domGrind] ++ input.drop 35)
  else
    none

@[simp] theorem literal_alpha_boundary_recovers_fold_work
    (digest : Digest256) (nonce : NonceBytes) :
    alphaBoundaryInputToFoldWork?
        (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce)) =
      some (bytes digest ++ (domGrind :: bytes nonce)) := by
  have dropExact :
      List.drop 35
          (bytes digest ++ domAbsorb :: foldWorkNonceLabel :: 0 ::
            bytes nonce) =
        bytes nonce := by
    simpa [bytes_length] using
      (List.drop_length_add_append (l₁ := bytes digest)
        (l₂ := domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce) 3)
  have takeExact :
      List.take 32
          (bytes digest ++ domAbsorb :: foldWorkNonceLabel :: 0 ::
            bytes nonce) = bytes digest := by
    calc
      _ = List.take 32 (bytes digest) :=
        List.take_append_of_le_length (by simp [bytes_length])
      _ = bytes digest := by simp [bytes_length]
  have condition :
      (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce)).length =
          43 ∧
        (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce))[32]? =
          some domAbsorb ∧
        (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce))[33]? =
          some foldWorkNonceLabel ∧
        (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce))[34]? =
          some 0 := by
    simp [bytes_length]
  unfold alphaBoundaryInputToFoldWork?
  rw [if_pos condition, takeExact, dropExact]
  simp [List.append_assoc]

/-- Pre-answer classification of the first selected-candidate exposure. -/
inductive FoldCandidateAnchorKind where
  | work (boundaryInput : ShaInput)
  | boundary (workInput : ShaInput)
  deriving DecidableEq, Repr

def foldCandidateAnchorKind? (input : ShaInput) :
    Option FoldCandidateAnchorKind :=
  match foldWorkInputToAlphaBoundary? input with
  | some boundary => some (.work boundary)
  | none =>
      match alphaBoundaryInputToFoldWork? input with
      | some work => some (.boundary work)
      | none => none

@[simp] theorem literal_fold_work_anchor_kind
    (digest : Digest256) (nonce : NonceBytes) :
    foldCandidateAnchorKind? (bytes digest ++ domGrind :: bytes nonce) =
      some (.work
        (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce))) := by
  rw [foldCandidateAnchorKind?]
  rw [show foldWorkInputToAlphaBoundary?
      (bytes digest ++ domGrind :: bytes nonce) =
        some (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce)) by
    simpa [List.append_assoc] using
      literal_fold_work_arms_exact_alpha_boundary digest nonce]

@[simp] theorem literal_alpha_boundary_anchor_kind
    (digest : Digest256) (nonce : NonceBytes) :
    foldCandidateAnchorKind?
        (bytes digest ++
          (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce)) =
      some (.boundary (bytes digest ++ domGrind :: bytes nonce)) := by
  have workParserNone :
      foldWorkInputToAlphaBoundary?
          (bytes digest ++
            (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce)) =
        none := by
    simp [foldWorkInputToAlphaBoundary?, bytes_length]
  rw [foldCandidateAnchorKind?, workParserNone,
    literal_alpha_boundary_recovers_fold_work]

/-- `none` is the selected fold-work answer; `some block` is one of the four
ordinary alpha-zero output blocks. -/
abbrev FoldOneFoldDigestSlot := Option (Fin 4)

/-- Causal state for either chronological order of one selected candidate. -/
structure BidirectionalFoldAlphaMemory where
  foldUsed : Bool
  expectedWork : Option ShaInput
  alpha : FoldArmedAlphaZeroMemory
  deriving DecidableEq

def inactiveBidirectionalFoldAlphaMemory : BidirectionalFoldAlphaMemory :=
  { foldUsed := false
    expectedWork := none
    alpha := inactiveFoldArmedAlphaZeroMemory }

def bidirectionalAlphaState
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory) :
    IndexedUnifiedExposureState globalOracleCalls FoldArmedAlphaZeroMemory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.alpha }

def currentBidirectionalInput?
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory) : Option ShaInput :=
  unifiedInputBeforeAnswer? transitionFuel state.cursor

/-- A later exact work sibling is named once.  Otherwise the established
alpha producer inventory chooses an output-block slot. -/
def bidirectionalFoldAlphaPreferred
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory) : Option FoldOneFoldDigestSlot :=
  let current := currentBidirectionalInput? transitionFuel state
  if atAnchor : state.exposureIndex = anchorIndex then
    match current.bind foldCandidateAnchorKind? with
    | some (.work _) => some none
    | some (.boundary _) | none => none
  else if state.memory.foldUsed = false ∧
      current = state.memory.expectedWork then
    some none
  else
    (alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState (bidirectionalAlphaState state))).map some

/-- Install a boundary producer when the boundary is the first selected-pair
exposure.  Its answer is available only after the pre-answer slot decision. -/
def installBoundaryAnchor
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (input workInput : ShaInput) (answer : Digest256) :
    BidirectionalFoldAlphaMemory :=
  { foldUsed := state.memory.foldUsed
    expectedWork := some workInput
    alpha :=
      { expectedBoundary := some input
        seenMachine := rememberCurrentMachine transitionFuel
          (bidirectionalAlphaState state) answer
        alpha :=
          { producers :=
              [{ digest := answer, block := 0, sourceInput := input }]
            usedSlots := state.memory.alpha.alpha.usedSlots } } }

def bidirectionalFoldAlphaAfterMemory
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256) : BidirectionalFoldAlphaMemory :=
  let current := currentBidirectionalInput? transitionFuel state
  if atAnchor : state.exposureIndex = anchorIndex then
    match current with
    | none => state.memory
    | some input =>
        match foldCandidateAnchorKind? input with
        | some (.work _boundary) =>
            { foldUsed := true
              expectedWork := state.memory.expectedWork
              alpha := armFoldAlphaMemory transitionFuel
                (bidirectionalAlphaState state) answer }
        | some (.boundary workInput) =>
            installBoundaryAnchor transitionFuel state input workInput answer
        | none => state.memory
  else
    let nextAlpha := foldArmedAlphaAfterMemory transitionFuel
      (bidirectionalAlphaState state) answer
    let consumesWork := state.memory.foldUsed = false ∧
      current = state.memory.expectedWork
    { foldUsed := state.memory.foldUsed || decide consumesWork
      expectedWork := state.memory.expectedWork
      alpha := nextAlpha }

/-- Five-coordinate causal controller valid for work-first and
boundary-first selected candidates. -/
def bidirectionalFoldAlphaController
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldOneFoldDigestSlot BidirectionalFoldAlphaMemory where
  preferredSlot := bidirectionalFoldAlphaPreferred transitionFuel anchorIndex
  afterMemory := bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex

@[simp] theorem bidirectional_preferred_at_literal_work_anchor
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (digest : Digest256) (nonce : NonceBytes)
    (atAnchor : state.exposureIndex = anchorIndex)
    (inputExact : currentBidirectionalInput? transitionFuel state =
      some (bytes digest ++ domGrind :: bytes nonce)) :
    (bidirectionalFoldAlphaController transitionFuel anchorIndex).preferredSlot
        state = some none := by
  simp [bidirectionalFoldAlphaController, bidirectionalFoldAlphaPreferred,
    atAnchor, inputExact]

@[simp] theorem bidirectional_preferred_at_literal_boundary_anchor
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (digest : Digest256) (nonce : NonceBytes)
    (atAnchor : state.exposureIndex = anchorIndex)
    (inputExact : currentBidirectionalInput? transitionFuel state =
      some (bytes digest ++
        (domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce))) :
    (bidirectionalFoldAlphaController transitionFuel anchorIndex).preferredSlot
        state = none := by
  simp [bidirectionalFoldAlphaController, bidirectionalFoldAlphaPreferred,
    atAnchor, inputExact]

end

#print axioms literal_alpha_boundary_recovers_fold_work
#print axioms literal_fold_work_anchor_kind
#print axioms literal_alpha_boundary_anchor_kind
#print axioms bidirectional_preferred_at_literal_work_anchor
#print axioms bidirectional_preferred_at_literal_boundary_anchor

end AspisK1.V7Tag73BidirectionalFoldAlphaController
