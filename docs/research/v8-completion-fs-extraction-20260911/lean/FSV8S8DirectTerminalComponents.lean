import SelectedTerminalClaimMapping
import SelectedTerminalPublicContext
import SelectedPoseidonCoordinateSlice
import SelectedCopyResidualCallback

/-!
# Direct selected-terminal components from the same-body claims

This leaf evaluates the projected Poseidon and Copy parts of
`pair_forest_semantic_terminal::composition_parts` directly from the 84
claims parsed from the submitted body.  In particular it does not recover a
Boolean C1 table, take `C1InitialMessages`, or accept helper/mask values from a
caller.

The remaining direct semantic-terminal work is intentionally visible:

* the 24 packed payment-semantic lanes still need a claims/public evaluator;
* the selected hiding polynomial still needs a literal evaluator from
  `c1`, `maskOnly`, `g`, and the point;
* the protocol's concrete Poseidon constant table must be connected to the
  abstract `RoundConstants` argument below; and
* the dynamic root must carry the independently decoded public/transition
  inputs (it currently carries only the 32-byte binding).

Thus the declarations here are component evaluators, not terminal acceptance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

namespace AspisV8Completion.FSV8S8DirectTerminalComponents

open scoped BigOperators
open AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedWeightedCopyRows
open FSLiveSemanticTerminalInput
open SelectedTerminalClaimMapping
open SelectedTerminalPublicContext
open SelectedPoseidonGenericAlgebra
open SelectedPoseidonCoordinateSlice
open SelectedCopySingleEndpoint
open SelectedCopyPatternValuesLiteral
open SelectedCopyLinkConstants
open SelectedCopyResidualCallback

abbrev K := FSLiveSemanticTerminalInput.K

noncomputable section

/-- One direct projected-Poseidon coordinate, with all three views taken from
the submitted body's claim array. -/
def poseidonCoordinate (rc : RoundConstants) (input : Input)
    (lane : Fin 16) : K :=
  residualCoordinate baseToK rc (blockValue input.z) (selectorValue input.z)
    (openings input).z (openings input).succZ (openings input).xor12Z lane

/-- The four source coordinates of one packed Poseidon lane. -/
def poseidonLane (rc : RoundConstants) (input : Input) (group : Fin 4) : K :=
  literalPack (fun slot =>
    poseidonCoordinate rc input
      (AspisV8.SelectedConcreteRowLanes.stateLane group slot))

/-- The compressed value used by every producer/consumer occurrence.  Rust
computes the fourteen pattern values once from `openings.z`; endpoint
selectors, rather than endpoint-specific table rows, are then accumulated. -/
def copyCompressed (input : Input) (index : Fin 136) : K :=
  (rustTag index : K) +
    rustPatternValueLiteral (fun column =>
      if bound : column < 16 then (openings input).z ⟨column, bound⟩ else 0)
      input.lambda (rustProducerEndpoint index).pattern

/-- Direct transcription of the selected 136-link Copy loop from the actual
opening vector.  Producer and consumer pattern identifiers agree in the
frozen link table, but the consumer identifier is used explicitly below so
that this declaration retains the source roles. -/
def directCopyRow (input : Input) (transition : TransitionInput) : Row K where
  producerValue slot := ∑ index : Fin 136,
    sourceEndpointContribution input.z (rustProducerEndpoint index) slot
      ((rustTag index : K) +
        rustPatternValueLiteral
          (fun column =>
            if bound : column < 16 then (openings input).z ⟨column, bound⟩ else 0)
          input.lambda (rustProducerEndpoint index).pattern)
  producerWeight slot := ∑ index : Fin 136,
    sourceEndpointContribution input.z (rustProducerEndpoint index) slot
      (rustPublicWeight .transfer transition.live.nextPairIndex index)
  consumerValue slot := ∑ index : Fin 136,
    sourceEndpointContribution input.z (rustConsumerEndpoint index) slot
      ((rustTag index : K) +
        rustPatternValueLiteral
          (fun column =>
            if bound : column < 16 then (openings input).z ⟨column, bound⟩ else 0)
          input.lambda (rustConsumerEndpoint index).pattern)
  consumerWeight slot := ∑ index : Fin 136,
    sourceEndpointContribution input.z (rustConsumerEndpoint index) slot
      (rustPublicWeight .transfer transition.live.nextPairIndex index)

/-- Exact selected Copy callback result from claims and public transition.
The helper argument is the same-body H1 claim at column 26. -/
def copyResidual (input : Input) (transition : TransitionInput) : K :=
  AspisV8Completion.SelectedCopyActiveExecutable.rustSelectedCopyActive input.z *
    rustCopyResidual (directCopyRow input transition) (h1 input) input.chi

def copyActive (input : Input) : K :=
  AspisV8Completion.SelectedCopyActiveExecutable.rustSelectedCopyActive input.z

structure Components where
  poseidon : Fin 4 -> K
  copyResidual : K
  copyActive : K

def evaluate (rc : RoundConstants) (input : Input)
    (transition : TransitionInput) : Components where
  poseidon := poseidonLane rc input
  copyResidual := copyResidual input transition
  copyActive := copyActive input

@[simp] theorem evaluate_poseidon (rc : RoundConstants) (input : Input)
    (transition : TransitionInput) (group : Fin 4) :
    (evaluate rc input transition).poseidon group = poseidonLane rc input group := rfl

@[simp] theorem evaluate_copyResidual (rc : RoundConstants) (input : Input)
    (transition : TransitionInput) :
    (evaluate rc input transition).copyResidual = copyResidual input transition := rfl

@[simp] theorem evaluate_copyActive (rc : RoundConstants) (input : Input)
    (transition : TransitionInput) :
    (evaluate rc input transition).copyActive = copyActive input := rfl

/-- The direct evaluator depends on the actual same-body claim projections;
there is no full trace table or separately supplied helper in its interface. -/
theorem evaluate_uses_literal_claims (rc : RoundConstants) (input : Input)
    (transition : TransitionInput) :
    (evaluate rc input transition).copyResidual =
      AspisV8Completion.SelectedCopyActiveExecutable.rustSelectedCopyActive input.z *
        rustCopyResidual (directCopyRow input transition) (input.claims 0 26) input.chi := by
  rfl

#print axioms evaluate_poseidon
#print axioms evaluate_copyResidual
#print axioms evaluate_copyActive
#print axioms evaluate_uses_literal_claims

end
end AspisV8Completion.FSV8S8DirectTerminalComponents
