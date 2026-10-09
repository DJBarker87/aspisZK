import SelectedEarlyC1Amounts
import SelectedOutputNotes

/-! Source-review draft: SAME early-C1 table -> actual decoded recipient
and change note openings. The four full-state note carry links are derived
from the selected weighted registry. Canonical raw representatives and their
exact re-encoding are constructed, not assumed. Remaining semantic gates,
public bindings and the previous strict-amount endpoint stay explicit.
No acceptance, component-own-support recovery, or full validator is claimed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedEarlyC1Outputs
open Polynomial Finset
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7ExtractedLaneWords AspisPool.V7FixedWidth29TupleList
open AspisPool.V7C1SubfieldRecovery
open AspisV8.EarlyC1Family AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedWeightedCopyCore AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedCopyLayout AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedCopyAliases AspisV8.SelectedCopyAliasQM31
open AspisV8.SelectedPaymentRecovery AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedOutputNotes AspisV8.SelectedNoteRecovery
open AspisV8.PositivePackBinding
noncomputable section

def rawSemanticTable (candidate : C1InitialMessages) : Nat → Nat → Nat :=
  fun row column => (semanticTable candidate row column).val

theorem raw_canonical (candidate : C1InitialMessages) (row column : Nat) :
    rawSemanticTable candidate row column < p := ZMod.val_lt _

/-- Totalized rows included: the canonical representative recovers exactly
the original field table, not just values at the eventual decoder reads. -/
theorem rawTable_exact (candidate : C1InitialMessages) :
    SelectedOutputNotes.rawTable (rawSemanticTable candidate) = semanticTable candidate := by
  funext row column
  exact ZMod.natCast_zmod_val _

def carryIndex (which step : Fin 2) : Fin 136 := ⟨3 + 2 * which.val + step.val, by omega⟩

/-- Four public metadata checks for source indices 3,4,5,6. The first two
are transfer-only; the latter two have constant weight one. Patterns are
the actual full sixteen-column, zero-offset source tuples. -/
theorem output_carry_shape : ∀ which step : Fin 2,
    transferKind (selectedKind (carryIndex which step)) = true ∧
    (producer (carryIndex which step)).row.val = 16 * (outputBlock which + step.val) + 11 ∧
    (consumer (carryIndex which step)).row.val = 16 * (outputBlock which + step.val + 1) ∧
    sourcePatterns (producer (carryIndex which step)).pattern = ⟨16, 0, 0⟩ ∧
    sourcePatterns (consumer (carryIndex which step)).pattern = ⟨16, 0, 0⟩ := by
  decide

/-- Derive all 64 scalar carry aliases on the actual recovered table.
Only equalities are projected; no arbitrary QM31 multiplicative projection
or independent-basis assumption is used. -/
theorem weighted_aliases_supply_output_carries (candidate : C1InitialMessages)
    (appendIndex : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer appendIndex)
    (which step : Fin 2) (lane : Fin 16) :
    semanticTable candidate (16 * (outputBlock which + step.val) + 11) lane.val -
      semanticTable candidate (16 * (outputBlock which + step.val + 1)) lane.val = 0 := by
  obtain ⟨kind, sourceRow, targetRow, sourcePattern, targetPattern⟩ :=
    output_carry_shape which step
  have weight : selectedWeight (K := QM31Exact) .transfer appendIndex
      (carryIndex which step) = 1 := transfer_kind_weight _ appendIndex kind
  have sourceEq : patternLimb (memberTable candidate) (producer (carryIndex which step)) lane =
      memberTable candidate (producer (carryIndex which step)).row lane.val := by
    simp only [patternLimb, sourcePattern, lane.isLt, if_true, Nat.zero_add,
      Nat.cast_zero, ite_self, add_zero]
  have targetEq : patternLimb (memberTable candidate) (consumer (carryIndex which step)) lane =
      memberTable candidate (consumer (carryIndex which step)).row lane.val := by
    simp only [patternLimb, targetPattern, lane.isLt, if_true, Nat.zero_add,
      Nat.cast_zero, ite_self, add_zero]
  have residual := aliases (carryIndex which step) lane
  rw [weight, one_mul, sourceEq, targetEq] at residual
  have projected := congrArg (fun value : QM31Exact => value.re.re) (sub_eq_zero.mp residual)
  rw [← semanticTable_read, ← semanticTable_read, sourceRow, targetRow] at projected
  exact sub_eq_zero.mpr projected

/-- Source output-note checks other than copy. The carry fields are not
assumed; they will be provided by the selected copy protocol's alias branch. -/
structure OutputSemanticChecks (rc : RoundConstants) (candidate : C1InitialMessages) : Prop where
  pairs : ∀ which : Fin 2, ∀ j : Fin 3,
    BlockResiduals rc (semanticTable candidate) (outputBlock which + j.val)
  initial : ∀ which : Fin 2, ∀ i : Fin 16,
    semanticTable candidate (16 * outputBlock which) i.val - initState DOM_NOTE 18 i = 0
  tailZero : ∀ which : Fin 2, ∀ i : Fin 6,
    semanticTable candidate (16 * (outputBlock which + 2) + 12) (i.val + 2) = 0

theorem output_residuals_from_selected_copy
    (rc : RoundConstants) (candidate : C1InitialMessages) (appendIndex : Nat)
    (semantic : OutputSemanticChecks rc candidate)
    (aliases : WeightedAliases (memberTable candidate) .transfer appendIndex) :
    ∀ which, OutputResiduals rc (semanticTable candidate) (outputBlock which) := by
  intro which
  exact ⟨semantic.pairs which, semantic.initial which,
    weighted_aliases_supply_output_carries candidate appendIndex aliases which,
    semantic.tailZero which⟩

def decodedOutput (candidate : C1InitialMessages) (which : Fin 2) : NoteFields :=
  decodeRawNote (rawSemanticTable candidate) (outputBlock which)

def amountIndex (which : Fin 2) : Fin 3 := ⟨which.val + 1, by omega⟩

theorem output_amount_cell : ∀ which : Fin 2,
    amountRow (outputBlock which) = SelectedPaymentRecovery.sourceRow (amountIndex which) := by
  decide

theorem decoded_output_value (candidate : C1InitialMessages) (which : Fin 2) :
    (decodedOutput candidate which).value = decodedValue (semanticTable candidate) (amountIndex which) := by
  change (semanticTable candidate (amountRow (outputBlock which)) 0).val =
    (semanticTable candidate (SelectedPaymentRecovery.sourceRow (amountIndex which)) 0).val
  rw [output_amount_cell]

def OutputFacts (rc : RoundConstants) (candidate : C1InitialMessages)
    (asset : F) (commitments : Fin 2 → Digest) : Prop :=
  (∀ which, 0 < (decodedOutput candidate which).value ∧
    (decodedOutput candidate which).value < 2^30 ∧
    commitments which = noteHash rc (decodedOutput candidate which).ownerKey
      ((decodedOutput candidate which).value : F) asset (decodedOutput candidate which).salt) ∧
  rawSemanticTable candidate 44 0 =
    (decodedOutput candidate 0).value + (decodedOutput candidate 1).value ∧
  (decodedOutput candidate 0).value + (decodedOutput candidate 1).value < 2^32

/-- Canonical raw decoding and the note openings use one table. AmountFacts
is exactly the conclusion of the preceding checked amount bridge, not an
assumption that either output note or the complete witness is valid. -/
theorem output_facts_of_aliases
    (rc : RoundConstants) (candidate : C1InitialMessages) (appendIndex : Nat)
    (amounts : AmountFacts (semanticTable candidate))
    (semantic : OutputSemanticChecks rc candidate)
    (aliases : WeightedAliases (memberTable candidate) .transfer appendIndex)
    (asset : F) (commitments : Fin 2 → Digest)
    (assets : ∀ which, semanticTable candidate (amountRow (outputBlock which)) 1 - asset = 0)
    (binding : ∀ which, ∀ i : Fin 8,
      semanticTable candidate (16 * (outputBlock which + 2) + 11) i.val - commitments which i = 0) :
    OutputFacts rc candidate asset commitments := by
  have notes := output_residuals_from_selected_copy rc candidate appendIndex semantic aliases
  have openings := both_raw_transfer_output_openings rc (rawSemanticTable candidate)
    (fun row _ column _ => raw_canonical candidate row column)
    (by simpa only [rawTable_exact] using notes) asset commitments
    (by simpa only [rawSemanticTable, ZMod.natCast_zmod_val] using assets)
    (by simpa only [rawSemanticTable, ZMod.natCast_zmod_val] using binding)
  refine ⟨?_, ?_, ?_⟩
  · intro which
    refine ⟨?_, ?_, openings which⟩
    · rw [decoded_output_value]
      exact (amounts.1 (amountIndex which)).1
    · rw [decoded_output_value]
      exact (amounts.1 (amountIndex which)).2
  · rw [decoded_output_value, decoded_output_value]
    exact amounts.2.1
  · rw [decoded_output_value, decoded_output_value]
    exact amounts.2.2

/-- The same pre-lambda member and adaptive helper feed both stages. The
existing collision event is retained unchanged and is not charged twice.
No owner/input-path, occupied-pair, afterstate or full validator claim. -/
theorem member_outputs_or_copy_collision
    (rc : RoundConstants) (c1 : C1InitialWords) (candidate : C1InitialMessages)
    (member : candidate ∈ EarlyC1Family.family c1)
    (baseWord : ∀ column index, projectBase (c1 column index) = c1 column index)
    (appendIndex : Nat) (lambdas chis : Finset QM31Exact) (lambda chi : QM31Exact)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → QM31Exact)
    (copy : CopyConditions candidate .transfer appendIndex lambda chi helper)
    (amounts : AmountFacts (semanticTable candidate))
    (semantic : OutputSemanticChecks rc candidate)
    (asset : F) (commitments : Fin 2 → Digest)
    (assets : ∀ which, semanticTable candidate (amountRow (outputBlock which)) 1 - asset = 0)
    (binding : ∀ which, ∀ i : Fin 8,
      semanticTable candidate (16 * (outputBlock which + 2) + 11) i.val - commitments which i = 0) :
    (∀ row : Fin 1024, ∀ column : Fin 16,
      liftBase (semanticTable candidate row.val column.val) = memberTable candidate row column.val) ∧
    (OutputFacts rc candidate asset commitments ∨
      (lambda, chi) ∈ collisionPairs c1 .transfer appendIndex lambdas chis) := by
  refine ⟨semanticTable_embeds c1 candidate member baseWord, ?_⟩
  rcases source_member_covered c1 .transfer appendIndex lambdas chis lambda chi
      lambdaMember chiMember candidate member helper copy with aliases | collision
  · exact Or.inl (output_facts_of_aliases rc candidate appendIndex amounts semantic aliases
      asset commitments assets binding)
  · exact Or.inr collision

#print axioms raw_canonical
#print axioms rawTable_exact
#print axioms output_carry_shape
#print axioms weighted_aliases_supply_output_carries
#print axioms output_residuals_from_selected_copy
#print axioms output_amount_cell
#print axioms decoded_output_value
#print axioms output_facts_of_aliases
#print axioms member_outputs_or_copy_collision
end
end AspisV8.SelectedEarlyC1Outputs
