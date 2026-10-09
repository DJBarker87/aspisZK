import SameBodyAuthenticatedFold

/-! DRAFT pending a focused historical-variant check.
Same-record residuals and the degree-q-shaped shifted scalar transport to the
authenticated prefix quotient, with the same concrete authentication union.
Arbitrary final/prior/rho are allowed pointwise; this theorem makes no claim
that the final was fixed before any actual FS challenge. It does not yet
identify the positive source foldl update with the finite sums below.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
namespace AspisV8.SameBodyAuthenticatedResidual
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun
open AspisV8.SelectedMultiproofOpeningEquality AspisV8.PackedQueryRecord
open AspisV8.SameBodyAuthenticatedSlots AspisV8.SameBodyAuthenticatedFold
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional
open scoped BigOperators
noncomputable section
abbrev K := QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def fixedFold (d : Data (K := K)) (c1Prefix c2Prefix : AnswerPrefix)
    (wire : Wire) (alpha : K) : K → K :=
  (SelectedReceivedOracle.oracle (0 : Fin 1024 → K)
    (SelectedQuotientOriginal.virtual d (prefixBatch c1Prefix c2Prefix wire d.gamma))).folded alpha

def recordResidual (d : Data (K := K)) (decoded : Fin 22 → Decoded)
    (query : Fin 22 → Position) (out : List K × List M31Exact)
    (alpha : K) (final : Fin 256 → K) (i : Fin 22) : K :=
  exactFinalLinear final (query i) - SelectedPackedQueryBridge.recordFold d decoded query out alpha i

attribute [local irreducible] SelectedPackedQueryBridge.recordFold
attribute [local irreducible] QueriedResidual.sourceFold

theorem same_body_authenticated_residual_or_failure
    (view : RawHashInput → Digest208) (body : List Byte)
    (query : Fin 22 → Position) (merkle : SuccessfulMerkleRun view query body)
    (c1Prefix c2Prefix : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1Prefix, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1Prefix) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog
      (MinimalMultiproofPaths.leafLog query (wireRecords merkle.wire) ++ merkle.trace) fullLog)
    (canonical : (parseRecords merkle.wire).isSome = true)
    (d : Data (K := K)) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c
      (SelectedQueryBuffer.points query) = some out)
    (alpha prior rho : K) (final : Fin 256 → K) :
    AuthenticationFailure view c1Prefix c2Prefix (wireRoots merkle.wire) fullLog query ∨
      ∃ decoded : Fin 22 → Decoded,
        parseRecords merkle.wire = some decoded ∧
        (∀ i, merkle.wire.record i = PackedQueryRecord.bodyRecord body i) ∧
        (∀ i : Fin 22, recordResidual d decoded query out alpha final i =
          PostQueryFunctional.residual final (fun j => storedPoint (K := K) (query j))
            (fixedFold d c1Prefix c2Prefix merkle.wire alpha) i) ∧
        (prior - rho * ∑ i : Fin 22,
          recordResidual d decoded query out alpha final i * rho^i.val) =
        (prior - rho * ∑ i : Fin 22,
          PostQueryFunctional.residual final (fun j => storedPoint (K := K) (query j))
            (fixedFold d c1Prefix c2Prefix merkle.wire alpha) i * rho^i.val) := by
  rcases same_body_authenticated_fold_or_failure view body query merkle
      c1Prefix c2Prefix fullLog c1Answers c2Answers c1Included c2Included
      callsIncluded canonical d out inverse alpha with bad | good
  · exact Or.inl bad
  · obtain ⟨decoded, parsed, bodyRecords, folds⟩ := good
    have residuals : ∀ i : Fin 22, recordResidual d decoded query out alpha final i =
        PostQueryFunctional.residual final (fun j => storedPoint (K := K) (query j))
          (fixedFold d c1Prefix c2Prefix merkle.wire alpha) i := by
      intro i
      unfold recordResidual
      rw [folds i]
      simp only [PostQueryFunctional.residual, fixedFold,
        SelectedReceivedOracle.final_evaluation]
    refine Or.inr ⟨decoded,parsed,bodyRecords,residuals,?_⟩
    apply congrArg (fun s : K => prior-rho*s)
    apply Finset.sum_congr rfl
    intro i _
    rw [residuals i]

#print same_body_authenticated_residual_or_failure
#print axioms same_body_authenticated_residual_or_failure
end
end AspisV8.SameBodyAuthenticatedResidual
