import SameBodyOpenedRun
import SameBodyQueryClaimExact

/-! DRAFT pending focused historical compilation.
The positive source-shaped query update consumes only the successful opened
pipeline's values. The final polynomial is read from that SAME parsed wire.
Data/query/alpha/rho/prior and chronological source/hash coupling remain
explicit boundaries. This is a deterministic query-discrepancy endpoint,
not full verifier acceptance or a challenge-distribution theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
namespace AspisV8.SameBodyOpenedQueryUpdate
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31Representation
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.SameBodyAuthenticatedSlots AspisV8.SameBodyOpenedRun
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional
open AspisV8Completion.SameBodyQueryClaimExact
open scoped BigOperators
noncomputable section
abbrev K := QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def finalFromWire (result : Output) : Fin 256 → K :=
  fun i => result.wire.values.getD (441+i.val) 0

def positiveUpdate (result : Output) (d : Data (K := K))
    (query : Fin 22 → Position) (alpha prior rho : K) : K :=
  AspisV8Completion.SameBodyQueryClaim.injectClaim (ringArithmetic (1/4 : K))
    prior rho (opened result d query alpha)

def fixedReceived (result : Output) (d : Data (K := K))
    (c1Prefix c2Prefix : AnswerPrefix) (alpha : K) : K → K :=
  (SelectedReceivedOracle.oracle (0 : Fin 1024 → K)
    (SelectedQuotientOriginal.virtual d
      (prefixBatch c1Prefix c2Prefix result.wire d.gamma))).folded alpha

/-- Every final coefficient is the canonical decoded body field, not a
default or a second separately supplied final polynomial on successful runs. -/
theorem finalFromWire_canonical (view : RawHashInput → Digest208) (body : List Byte)
    (query : Fin 22 → Position) (d : Data (K := K)) (result : Output)
    (success : run view body query d = some result) (i : Fin 256) :
    decodeQM31ExactLE (CanonicalRelationInput.fieldBytes body ⟨441+i.val, by omega⟩) =
      some (finalFromWire result i) :=
  (SelectedWireBytes.fixed_fields body result.wire
    (run_checks view body query d result success).1).2 ⟨441+i.val, by omega⟩

attribute [local irreducible] finalFromWire
attribute [local irreducible] SelectedPackedQueryBridge.recordFold
attribute [local irreducible] ringArithmetic
attribute [local irreducible] AspisV8Completion.SameBodyQueryClaim.injectClaim
attribute [local irreducible] opened exactFinalLinear

theorem successful_opened_query_update_or_failure
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
    (alpha prior rho : K) :
    AuthenticationFailure view c1Prefix c2Prefix (wireRoots result.wire) fullLog query ∨
      positiveUpdate result d query alpha prior rho -
        (∑ i : Fin 22, rho^(i.val+1)*exactFinalLinear (finalFromWire result) (query i)) =
      prior-rho*∑ i : Fin 22,
        PostQueryFunctional.residual (finalFromWire result)
          (fun j => storedPoint (K := K) (query j))
          (fixedReceived result d c1Prefix c2Prefix alpha) i * rho^i.val := by
  rcases run_authenticated_opened_or_failure view body query d result success
      c1Prefix c2Prefix fullLog c1Answers c2Answers c1Included c2Included
      callsIncluded alpha with bad | values
  · exact Or.inl bad
  · apply Or.inr
    have sums :
        (∑ i : Fin 22, (exactFinalLinear (finalFromWire result) (query i) -
          opened result d query alpha i) * rho^i.val) =
        ∑ i : Fin 22, PostQueryFunctional.residual (finalFromWire result)
          (fun j => storedPoint (K := K) (query j))
          (fixedReceived result d c1Prefix c2Prefix alpha) i * rho^i.val := by
      apply Finset.sum_congr rfl
      intro i _
      have sameResidual : exactFinalLinear (finalFromWire result) (query i) -
          opened result d query alpha i =
          PostQueryFunctional.residual (finalFromWire result)
            (fun j => storedPoint (K := K) (query j))
            (fixedReceived result d c1Prefix c2Prefix alpha) i := by
        rw [values i]
        simp only [PostQueryFunctional.residual, fixedReceived,
          SelectedReceivedOracle.final_evaluation]
      exact congrArg (fun x : K => x * rho^i.val) sameResidual
    unfold positiveUpdate
    rw [injectClaim_discrepancy (1/4 : K) prior rho
      (opened result d query alpha) (fun i => exactFinalLinear (finalFromWire result) (query i))]
    exact congrArg (fun s : K => prior-rho*s) sums

#print successful_opened_query_update_or_failure
#print axioms finalFromWire_canonical
#print axioms successful_opened_query_update_or_failure
end
end AspisV8.SameBodyOpenedQueryUpdate
