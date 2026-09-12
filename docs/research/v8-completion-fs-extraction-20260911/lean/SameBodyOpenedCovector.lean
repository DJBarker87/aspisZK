import SameBodyOpenedQueryUpdate
import ImageCallbackInterfaces

/-! DRAFT: full post-query covector discrepancy, not terminal acceptance.
The previous scalar leaf subtracts only injected final evaluations. Here the
whole updated functional is subtracted, preserving the arbitrary carried
ordinary/image discrepancy. The final and opened data come from the same
successful functional body run. Existing weight/prior remain explicit inputs:
their response0/public-image source producers are NOT assumed completed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
namespace AspisV8.SameBodyOpenedCovector
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCConcreteFoldLinearity
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.SameBodyAuthenticatedSlots AspisV8.SameBodyOpenedRun
open AspisV8.SameBodyOpenedQueryUpdate
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional
open AspisV8Completion.SameBodyQueryClaimExact
open scoped BigOperators
noncomputable section
abbrev K := QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def updatedWeights (weight : Fin 256 → K) (query : Fin 22 → Position)
    (rho : K) : Fin 256 → K :=
  fun i => weight i + ∑ j : Fin 22, rho^(j.val+1)*lineWeight (storedPoint (K := K) (query j)) i

attribute [local irreducible] finalFromWire
attribute [local irreducible] SelectedPackedQueryBridge.recordFold
attribute [local irreducible] ringArithmetic
attribute [local irreducible] AspisV8Completion.SameBodyQueryClaim.injectClaim
attribute [local irreducible] opened exactFinalLinear

theorem successful_opened_covector_or_failure
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
    (alpha prior rho : K) (weight : Fin 256 → K) :
    AuthenticationFailure view c1Prefix c2Prefix (wireRoots result.wire) fullLog query ∨
      positiveUpdate result d query alpha prior rho -
        (∑ i : Fin 256, finalFromWire result i * updatedWeights weight query rho i) =
      (prior-∑ i : Fin 256, finalFromWire result i*weight i) -
        rho*∑ j : Fin 22,
          PostQueryFunctional.residual (finalFromWire result)
            (fun k => storedPoint (K := K) (query k))
            (fixedReceived result d c1Prefix c2Prefix alpha) j * rho^j.val := by
  rcases run_authenticated_opened_or_failure view body query d result success
      c1Prefix c2Prefix fullLog c1Answers c2Answers c1Included c2Included
      callsIncluded alpha with bad | values
  · exact Or.inl bad
  · apply Or.inr
    have sums :
        (∑ j : Fin 22, ((∑ i : Fin 256, finalFromWire result i *
          lineWeight (storedPoint (K := K) (query j)) i) -
          opened result d query alpha j) * rho^j.val) =
        ∑ j : Fin 22, PostQueryFunctional.residual (finalFromWire result)
          (fun k => storedPoint (K := K) (query k))
          (fixedReceived result d c1Prefix c2Prefix alpha) j * rho^j.val := by
      apply Finset.sum_congr rfl
      intro j _
      have evaluation : (∑ i : Fin 256, finalFromWire result i *
          lineWeight (storedPoint (K := K) (query j)) i) =
          exactFinalLinear (finalFromWire result) (query j) :=
        (lineEval_dot (finalFromWire result) _).symm.trans
          (SelectedReceivedOracle.final_evaluation (finalFromWire result) (query j))
      have sameResidual :
          (∑ i : Fin 256, finalFromWire result i *
            lineWeight (storedPoint (K := K) (query j)) i) -
            opened result d query alpha j =
          PostQueryFunctional.residual (finalFromWire result)
            (fun k => storedPoint (K := K) (query k))
            (fixedReceived result d c1Prefix c2Prefix alpha) j := by
        rw [evaluation, values j]
        simp only [PostQueryFunctional.residual, fixedReceived,
          SelectedReceivedOracle.final_evaluation]
      exact congrArg (fun x : K => x * rho^j.val) sameResidual
    unfold positiveUpdate updatedWeights
    rw [injectClaim_exact]
    rw [ImageCallbackInterfaces.query_injection 256 22 (finalFromWire result) weight
      (fun j => lineWeight (storedPoint (K := K) (query j)))
      (opened result d query alpha) prior rho]
    rw [sums]

#print successful_opened_covector_or_failure
#print axioms successful_opened_covector_or_failure
end
end AspisV8.SameBodyOpenedCovector
