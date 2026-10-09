import SelectedEarlyC1InputPair
import SelectedEarlyC1Inputs
import EarlyC1StrongFamilyBridge

/-!
One fixed early-C1 table feeds the selected amount, input-note/nullifier,
occupied input-pair, and output-note decoders through ONE weighted-copy
alias branch.  The existing lambda/chi collision alternative is therefore
retained once, rather than independently for each payment fragment.

Semantic and public-binding residuals remain explicit premises.  This file
does not claim that verifier acceptance enforces them, construct the outer
Merkle/context witness, or prove settlement validity.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedEarlyC1PaymentFacts
open Polynomial Finset
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7ExtractedLaneWords AspisPool.V7FixedWidth29TupleList
open AspisPool.V7C1SubfieldRecovery
open AspisV8.EarlyC1Projection AspisV8.EarlyC1Family
open AspisV8.EarlyC1CopyCollision AspisV8.EarlyC1StrongFamilyBridge
open AspisV8.SelectedCopyAliases AspisV8.SelectedCopyAliasQM31
open AspisV8.SelectedPaymentRecovery AspisV8.PositivePackBinding
open AspisV8.SelectedAmountEndpoint
open AspisV8.SelectedNoteRecovery AspisV8.SelectedOutputNotes
open AspisV8.SelectedEarlyC1Amounts AspisV8.SelectedEarlyC1Inputs
open AspisV8.SelectedEarlyC1Outputs AspisV8.SelectedEarlyC1InputPair
noncomputable section

/-- The four deterministic payment fragments recovered from one table. -/
structure TransferFacts (rc : RoundConstants) (candidate : C1InitialMessages)
    (publicAsset : F) (publicNullifier : Digest)
    (commitments : Fin 2 → Digest) : Prop where
  amounts : AmountFacts (semanticTable candidate)
  inputs : InputFacts rc candidate publicAsset publicNullifier
  inputPair : InputPairFacts candidate
  outputs : OutputFacts rc candidate publicAsset commitments

/-- One actual alias witness supplies every copy equality used by the four
decoders.  Amount facts are derived first because output-note positivity and
conservation consume that exact result. -/
theorem transfer_facts_of_aliases
    (rc : RoundConstants) (candidate : C1InitialMessages) (appendIndex : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer appendIndex)
    (amountSemantic : AmountSemanticChecks (semanticTable candidate))
    (inputSemantic : InputSemanticChecks rc candidate)
    (pairSemantic : InputPairSemanticChecks candidate)
    (outputSemantic : OutputSemanticChecks rc candidate)
    (packedAsset : QM31Exact)
    (positive : tablePositivePack (semanticTable candidate) packedAsset = some 0)
    (publicAsset : F) (publicNullifier : Digest)
    (assetBinding : semanticTable candidate 44 1 - publicAsset = 0)
    (nullifierBinding : ∀ i : Fin 8,
      semanticTable candidate 427 i.val - publicNullifier i = 0)
    (commitments : Fin 2 → Digest)
    (outputAssets : ∀ which,
      semanticTable candidate (amountRow (outputBlock which)) 1 - publicAsset = 0)
    (outputBinding : ∀ which, ∀ i : Fin 8,
      semanticTable candidate (16 * (outputBlock which + 2) + 11) i.val -
        commitments which i = 0) :
    TransferFacts rc candidate publicAsset publicNullifier commitments := by
  have amountResiduals : CompiledAmountResiduals (semanticTable candidate) :=
    ⟨amountSemantic.boolean, amountSemantic.recomposition, amountSemantic.auxiliary,
      weighted_aliases_supply_amount_aliases candidate appendIndex aliases,
      amountSemantic.first, amountSemantic.second⟩
  have amounts : AmountFacts (semanticTable candidate) :=
    strict_decoded_amounts (semanticTable candidate) packedAsset amountResiduals positive
  refine ⟨amounts, ?_, ?_, ?_⟩
  · exact public_input_facts_of_aliases rc candidate appendIndex inputSemantic aliases
      publicAsset publicNullifier assetBinding nullifierBinding
  · exact input_pair_facts_of_aliases candidate appendIndex pairSemantic aliases
  · exact output_facts_of_aliases rc candidate appendIndex amounts outputSemantic aliases
      publicAsset commitments outputAssets outputBinding

/-- A member of the fixed pre-lambda/chi family gets one joint payment-facts
outcome or the one existing sequential copy-collision outcome. -/
theorem member_transfer_facts_or_copy_collision
    (rc : RoundConstants) (c1 : C1InitialWords) (candidate : C1InitialMessages)
    (member : candidate ∈ EarlyC1Family.family c1)
    (baseWord : ∀ column index, projectBase (c1 column index) = c1 column index)
    (appendIndex : Nat) (lambdas chis : Finset QM31Exact) (lambda chi : QM31Exact)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → QM31Exact)
    (copy : CopyConditions candidate .transfer appendIndex lambda chi helper)
    (amountSemantic : AmountSemanticChecks (semanticTable candidate))
    (inputSemantic : InputSemanticChecks rc candidate)
    (pairSemantic : InputPairSemanticChecks candidate)
    (outputSemantic : OutputSemanticChecks rc candidate)
    (packedAsset : QM31Exact)
    (positive : tablePositivePack (semanticTable candidate) packedAsset = some 0)
    (publicAsset : F) (publicNullifier : Digest)
    (assetBinding : semanticTable candidate 44 1 - publicAsset = 0)
    (nullifierBinding : ∀ i : Fin 8,
      semanticTable candidate 427 i.val - publicNullifier i = 0)
    (commitments : Fin 2 → Digest)
    (outputAssets : ∀ which,
      semanticTable candidate (amountRow (outputBlock which)) 1 - publicAsset = 0)
    (outputBinding : ∀ which, ∀ i : Fin 8,
      semanticTable candidate (16 * (outputBlock which + 2) + 11) i.val -
        commitments which i = 0) :
    (∀ row : Fin 1024, ∀ column : Fin 16,
      liftBase (semanticTable candidate row.val column.val) =
        memberTable candidate row column.val) ∧
    (TransferFacts rc candidate publicAsset publicNullifier commitments ∨
      (lambda, chi) ∈ collisionPairs c1 .transfer appendIndex lambdas chis) := by
  refine ⟨semanticTable_embeds c1 candidate member baseWord, ?_⟩
  rcases source_member_covered c1 .transfer appendIndex lambdas chis lambda chi
      lambdaMember chiMember candidate member helper copy with aliases | collision
  · exact Or.inl (transfer_facts_of_aliases rc candidate appendIndex aliases
      amountSemantic inputSemantic pairSemantic outputSemantic packedAsset positive
      publicAsset publicNullifier assetBinding nullifierBinding commitments
      outputAssets outputBinding)
  · exact Or.inr collision

/-- The strong early object discharges family membership itself; no
post-gamma tuple is moved backward through the transcript. -/
theorem early_transfer_facts_or_copy_collision
    (rc : RoundConstants) (c1 : C1InitialWords) (candidate : C1InitialMessages)
    (found : earlyC1 c1 = some candidate)
    (baseWord : ∀ column index, projectBase (c1 column index) = c1 column index)
    (appendIndex : Nat) (lambdas chis : Finset QM31Exact) (lambda chi : QM31Exact)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → QM31Exact)
    (copy : CopyConditions candidate .transfer appendIndex lambda chi helper)
    (amountSemantic : AmountSemanticChecks (semanticTable candidate))
    (inputSemantic : InputSemanticChecks rc candidate)
    (pairSemantic : InputPairSemanticChecks candidate)
    (outputSemantic : OutputSemanticChecks rc candidate)
    (packedAsset : QM31Exact)
    (positive : tablePositivePack (semanticTable candidate) packedAsset = some 0)
    (publicAsset : F) (publicNullifier : Digest)
    (assetBinding : semanticTable candidate 44 1 - publicAsset = 0)
    (nullifierBinding : ∀ i : Fin 8,
      semanticTable candidate 427 i.val - publicNullifier i = 0)
    (commitments : Fin 2 → Digest)
    (outputAssets : ∀ which,
      semanticTable candidate (amountRow (outputBlock which)) 1 - publicAsset = 0)
    (outputBinding : ∀ which, ∀ i : Fin 8,
      semanticTable candidate (16 * (outputBlock which + 2) + 11) i.val -
        commitments which i = 0) :
    (∀ row : Fin 1024, ∀ column : Fin 16,
      liftBase (semanticTable candidate row.val column.val) =
        memberTable candidate row column.val) ∧
    (TransferFacts rc candidate publicAsset publicNullifier commitments ∨
      (lambda, chi) ∈ collisionPairs c1 .transfer appendIndex lambdas chis) := by
  exact member_transfer_facts_or_copy_collision rc c1 candidate
    (some_early_member c1 candidate found) baseWord appendIndex lambdas chis lambda chi
    lambdaMember chiMember helper copy amountSemantic inputSemantic pairSemantic
    outputSemantic packedAsset positive publicAsset publicNullifier assetBinding
    nullifierBinding commitments outputAssets outputBinding

#print axioms transfer_facts_of_aliases
#print axioms member_transfer_facts_or_copy_collision
#print axioms early_transfer_facts_or_copy_collision
end
end AspisV8.SelectedEarlyC1PaymentFacts
