import FSLiveSemanticTerminalInput
import SelectedSemanticAfterstateChecksV2
import AspisFormal.Pool.V7SelectedEvaluatorSparsitySourceBridge

/-!
# Source-shaped transfer public/context projection for the selected terminal

This leaf models the deterministic part of `private_public` and
`validate_transition` used before the selected semantic terminal.  A successful
Boolean check constructs both the public projection consumed by the existing
semantic-row model and the dynamic digest-selector controls.  In particular,
the append index, its bits, and its carry are not independently supplied.

The byte/account authority of the input records and the literal Rust facts
that `u64::trailing_ones().min(20)` and bit shifts implement the mathematical
`carryIndex`/`Nat.testBit` operations remain source-refinement obligations.
No terminal acceptance or payment validity is assumed or concluded here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.SelectedTerminalPublicContext

open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticAfterstateChecks
open AspisPool.V7SelectedEvaluatorSparsitySourceBridge

noncomputable section

abbrev Bytes32 := Fin 32 -> UInt8

/-- Fields projected by Rust's private-transfer `SemanticPublic` constructor.
`pool` and `deploymentDomain` are retained because `validate_transition`
compares them to the independently supplied live account snapshot. -/
structure TransferPublicInput where
  pool : Bytes32
  deploymentDomain : Bytes32
  anchor : Digest
  nullifier : Digest
  asset : F
  recipient : Digest
  change : Digest

/-- The authoritative live-state fields read by `validate_transition`. -/
structure LiveSnapshotInput where
  pool : Bytes32
  deploymentDomain : Bytes32
  sequence : Nat
  nextPairIndex : Nat
  frontier : Fin 20 -> Digest

/-- The proposed afterstate fields used by the selected semantic terminal. -/
structure CandidateAfterstateInput where
  nextPairIndex : Nat
  nextRoot : Digest
  nextFrontier : Fin 20 -> Digest

structure TransitionInput where
  live : LiveSnapshotInput
  after : CandidateAfterstateInput

/-- The exact field projection consumed by the existing selected transfer-row
model.  Both output commitments and all transition values come from the same
public/context records passed to this function. -/
def publicProjection (pub : TransferPublicInput)
    (transition : TransitionInput) : Public where
  asset := pub.asset
  anchor := pub.anchor
  nullifier := pub.nullifier
  commitments := ![pub.recipient, pub.change]
  appendIndex := transition.live.nextPairIndex
  frontier := transition.live.frontier
  nextRoot := transition.after.nextRoot
  nextFrontier := transition.after.nextFrontier

def carryIndexOf (transition : TransitionInput) : Nat :=
  AspisV8.SelectedAppendAfterstate.carryIndex transition.live.nextPairIndex

/-- Exact static sibling expected by the Rust transition loop, expressed with
the mathematical bounded carry scan. -/
def expectedFrontier (transition : TransitionInput) (level : Fin 20) : Digest :=
  if level.val < carryIndexOf transition ||
      transition.live.nextPairIndex.testBit level.val = false then
    emptyRoot level
  else
    transition.live.frontier level

/-- Fail-closed, executable formulation of the comparisons in
`validate_transition`.  The skipped carry level is intentionally unchecked:
the authenticated semantic table binds it dynamically. -/
def validateTransition (pub : TransferPublicInput)
    (transition : TransitionInput) : Bool :=
  decide (
    transition.live.pool = pub.pool /\
    transition.live.deploymentDomain = pub.deploymentDomain /\
    transition.live.sequence = transition.live.nextPairIndex /\
    transition.live.nextPairIndex < 2^20 /\
    transition.after.nextPairIndex = transition.live.nextPairIndex + 1 /\
    forall level : Fin 20,
      ¬(level.val = carryIndexOf transition /\ carryIndexOf transition < 20) ->
        transition.after.nextFrontier level = expectedFrontier transition level)

/-- The bounded carry packaged for the frozen selector interface. -/
def digestCarry (transition : TransitionInput) : Fin 21 :=
  ⟨carryIndexOf transition, by
    unfold carryIndexOf AspisV8.SelectedAppendAfterstate.carryIndex
    have h := AspisV8.SelectedAppendAfterstate.carry_scan_bound
      transition.live.nextPairIndex.testBit 20
    omega⟩

theorem fin21_mk_val (n : Nat) (h : n < 21) :
    (⟨n, h⟩ : Fin 21).val = n := Eq.refl n

theorem digestCarry_val (transition : TransitionInput) :
    (digestCarry transition).val = carryIndexOf transition := by
  unfold digestCarry
  apply fin21_mk_val

/-- Dynamic controls passed to the frozen V7-selected digest selector
schedule.  Transfer always has a recipient; index bits and carry have one
source, the live snapshot's next-pair index. -/
def digestControl (transition : TransitionInput) : DigestControl where
  hasRecipient := true
  sourceBit := fun level => transition.live.nextPairIndex.testBit level.val
  carry := digestCarry transition

theorem validateTransition_true (pub : TransferPublicInput)
    (transition : TransitionInput)
    (accepted : validateTransition pub transition = true) :
    transition.live.pool = pub.pool /\
    transition.live.deploymentDomain = pub.deploymentDomain /\
    transition.live.sequence = transition.live.nextPairIndex /\
    transition.live.nextPairIndex < 2^20 /\
    transition.after.nextPairIndex = transition.live.nextPairIndex + 1 /\
    forall level : Fin 20,
      ¬(level.val = carryIndexOf transition /\ carryIndexOf transition < 20) ->
        transition.after.nextFrontier level = expectedFrontier transition level := by
  simpa only [validateTransition, decide_eq_true_eq] using accepted

/-- A successful source-shaped transition check constructs the exact
`SourceComparisons` premise used by the existing afterstate theorem. -/
theorem validateTransition_sourceComparisons (pub : TransferPublicInput)
    (transition : TransitionInput)
    (accepted : validateTransition pub transition = true) :
    SourceComparisons (publicProjection pub transition)
      transition.live.sequence transition.after.nextPairIndex (carryIndexOf transition) := by
  have h := validateTransition_true pub transition accepted
  refine ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro level notCarry
  have exact := h.2.2.2.2.2 level notCarry
  simpa only [publicProjection, expectedFrontier, carryIndexOf,
    Bool.or_eq_true, decide_eq_true_eq] using exact

theorem digestControl_sourceBit (pub : TransferPublicInput)
    (transition : TransitionInput)
    (level : Fin 20) :
    (digestControl transition).sourceBit level =
      (publicProjection pub transition).appendIndex.testBit level.val := by
  change transition.live.nextPairIndex.testBit level.val =
    transition.live.nextPairIndex.testBit level.val
  rfl

/-- The selected digest schedule's carry is definitionally the same bounded
scan used by the semantic afterstate theorem. -/
theorem digestControl_carry (transition : TransitionInput) :
    (digestControl transition).carry.val = carryIndexOf transition := by
  change (digestCarry transition).val = carryIndexOf transition
  exact digestCarry_val transition

/-- Same-body semantic success and a successful public transition check
construct one terminal input, its public projection, and its selector control.
This theorem does not say that the terminal accepted. -/
theorem successful_semantic_and_transition_construct_inputs
    (positiveTransfer : Bool)
    (binding : FSLiveSemanticPrefix.Binding)
    (body : List UInt8)
    (tape : FSBoundedTranscript.Tape)
    (oracle : FSBoundedTranscript.Oracle)
    (semantic : FSLiveSemanticPrefix.Success)
    (pub : TransferPublicInput) (transition : TransitionInput)
    (semanticAccepted :
      (FSOracleExecution.run tape
        (FSLiveSemanticPrefix.semanticScript positiveTransfer binding body) oracle).1 =
          some (.ok semantic))
    (transitionAccepted : validateTransition pub transition = true) :
    exists wire terminalInput,
      SameBodySemanticWire.parse body = some wire /\
      terminalInput = FSLiveSemanticTerminalInput.ofRun wire semantic /\
      SourceComparisons (publicProjection pub transition)
        transition.live.sequence transition.after.nextPairIndex (carryIndexOf transition) /\
      (digestControl transition).sourceBit =
        (fun level : Fin 20 =>
          (publicProjection pub transition).appendIndex.testBit level.val) /\
      (digestControl transition).carry.val = carryIndexOf transition := by
  obtain ⟨wire, terminalInput, parsed, input, _claims, _z, _carried⟩ :=
    FSLiveSemanticTerminalInput.successful_run_constructs_terminal_input
      positiveTransfer binding body tape oracle semantic semanticAccepted
  refine ⟨wire, terminalInput, parsed, input,
    validateTransition_sourceComparisons pub transition transitionAccepted,
    ?_, digestControl_carry transition⟩
  exact funext (digestControl_sourceBit pub transition)

#print axioms validateTransition_sourceComparisons
#print axioms digestControl_carry
#print axioms successful_semantic_and_transition_construct_inputs

end
end AspisV8Completion.SelectedTerminalPublicContext
