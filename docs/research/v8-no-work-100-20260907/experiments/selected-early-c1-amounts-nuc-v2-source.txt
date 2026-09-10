import EarlyC1CopyCollision
import SelectedAmountEndpoint

/-! Source-review draft: actual early-C1 member -> the selected amount
endpoint, outside the existing sequential copy collision set. Canonical
base descent identifies the projected table with the same member. The
remaining literal amount/positivity and copy/helper conditions stay visible;
no high-support batch is silently promoted to an own-supported tuple, and
neither verifier acceptance nor checked payment validity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedEarlyC1Amounts
open Polynomial Finset
open AspisV5ComponentCQM31TowerExact
open AspisFormal.ArithmetizationCore
open AspisPool.V7ExtractedLaneWords AspisPool.V7FixedWidth29TupleList
open AspisPool.V7C1SubfieldRecovery
open AspisV8.EarlyC1Family AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedCopyAliases AspisV8.SelectedCopyAliasQM31
open AspisV8.SelectedPaymentRecovery AspisV8.SelectedAmountEndpoint
open AspisV8.PositivePackBinding
noncomputable section

/-- The decoded base coordinate of the actual first-sixteen-column table.
The extension to rows outside 0..1023 is only a total mathematical view. -/
def semanticTable (p : C1InitialMessages) : SelectedPaymentRecovery.Table :=
  fun row column => if bounded : row < 1024 then
    (memberTable p ⟨row, bounded⟩ column).re.re else 0

theorem semanticTable_read (p : C1InitialMessages) (row : Fin 1024) (column : Nat) :
    semanticTable p row.val column = (memberTable p row column).re.re := by
  simp only [semanticTable, dif_pos row.isLt]

/-- The equality is derived from the fixed C1 member's OWN support and
base-valued received word. It is not an expected-trace correspondence. -/
theorem semanticTable_embeds (c1 : C1InitialWords) (p : C1InitialMessages)
    (member : p ∈ EarlyC1Family.family c1)
    (baseWord : ∀ column index, projectBase (c1 column index) = c1 column index)
    (row : Fin 1024) (column : Fin 16) :
    liftBase (semanticTable p row.val column.val) = memberTable p row column.val := by
  rw [semanticTable_read, memberTable_read]
  have base := congrFun (member_is_base c1 p member baseWord
    ⟨column.val, by omega⟩) row
  exact base

/-- Only seven finite cell-pair identities. The selected 136-link lookup
and transfer weights are already proved in SelectedCopyAliasQM31. -/
theorem amount_cell_conventions : ∀ edge : Fin 7,
    ((amountProducer edge).1.val, (amountProducer edge).2) = aliasProducer edge ∧
    ((amountConsumer edge).1.val, (amountConsumer edge).2) = aliasConsumer edge := by
  decide

/-- Actual selected weighted copy aliases discharge the amount endpoint's
individual singleton aliases on the SAME semantic table. No new registry
or assumed base-field algebraic independence is used. -/
theorem weighted_aliases_supply_amount_aliases (p : C1InitialMessages)
    (appendIndex : Nat)
    (aliases : WeightedAliases (memberTable p) .transfer appendIndex) :
    AliasResiduals (semanticTable p) := by
  intro edge lane
  have equal := transfer_amount_aliases (memberTable p) appendIndex aliases edge
  have projected := congrArg (fun value : QM31Exact => value.re.re) equal
  have cells := amount_cell_conventions edge
  have scalar : semanticTable p (aliasProducer edge).1 (aliasProducer edge).2 =
      semanticTable p (aliasConsumer edge).1 (aliasConsumer edge).2 := by
    rw [← cells.1, ← cells.2]
    simp only [semanticTable_read]
    exact projected
  by_cases first : lane.val = 0
  · simpa only [aliasResidual, singletonTuple, first, if_true, one_mul] using
      (sub_eq_zero.mpr scalar)
  · simp only [aliasResidual, singletonTuple, first, if_false, sub_self, mul_zero]

/-- Exactly the non-copy fields of CompiledAmountResiduals. These remain
literal semantic hypotheses; acceptance has not been shown to enforce them. -/
structure AmountSemanticChecks (t : SelectedPaymentRecovery.Table) : Prop where
  boolean : ∀ which bit, (bitValue t which bit)^2 - bitValue t which bit = 0
  recomposition : ∀ which, t (valueBase which) 10 - compiledReconstruction t which = 0
  auxiliary : ∀ which, t (valueBase which + 1) 10 = 0 ∧
    t (Nat.xor (valueBase which) 12) 10 = 0
  first : t 1014 0 - t 1014 1 - t 1014 2 = 0
  second : t 1015 0 - t 1015 1 = 0

def AmountFacts (t : SelectedPaymentRecovery.Table) : Prop :=
  (∀ which, 0 < decodedValue t which ∧ decodedValue t which < 2^30) ∧
    decodedValue t 0 = decodedValue t 1 + decodedValue t 2 ∧
    decodedValue t 1 + decodedValue t 2 < 2^32

/-- Covered-member deterministic endpoint. The helper can be adaptive,
but the member is selected from the actual pre-lambda C1 family. All four
slot poles and both helper boundaries remain in CopyConditions. The lambda
and chi collision alternative is preserved rather than assumed impossible.
The conclusion concerns amount checks only, not the complete validator. -/
theorem member_amounts_or_copy_collision
    (c1 : C1InitialWords) (p : C1InitialMessages)
    (member : p ∈ EarlyC1Family.family c1)
    (baseWord : ∀ column index, projectBase (c1 column index) = c1 column index)
    (appendIndex : Nat) (lambdas chis : Finset QM31Exact) (lambda chi : QM31Exact)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → QM31Exact)
    (copy : CopyConditions p .transfer appendIndex lambda chi helper)
    (semantic : AmountSemanticChecks (semanticTable p))
    (publicAsset : QM31Exact)
    (positive : tablePositivePack (semanticTable p) publicAsset = some 0) :
    (∀ row : Fin 1024, ∀ column : Fin 16,
      liftBase (semanticTable p row.val column.val) = memberTable p row column.val) ∧
    (AmountFacts (semanticTable p) ∨
      (lambda, chi) ∈ collisionPairs c1 .transfer appendIndex lambdas chis) := by
  refine ⟨semanticTable_embeds c1 p member baseWord, ?_⟩
  rcases source_member_covered c1 .transfer appendIndex lambdas chis lambda chi
      lambdaMember chiMember p member helper copy with aliases | collision
  · left
    have constraints : CompiledAmountResiduals (semanticTable p) :=
      ⟨semantic.boolean, semantic.recomposition, semantic.auxiliary,
        weighted_aliases_supply_amount_aliases p appendIndex aliases,
        semantic.first, semantic.second⟩
    exact strict_decoded_amounts (semanticTable p) publicAsset constraints positive
  · exact Or.inr collision

#print axioms semanticTable_read
#print axioms semanticTable_embeds
#print axioms amount_cell_conventions
#print axioms weighted_aliases_supply_amount_aliases
#print axioms member_amounts_or_copy_collision
end
end AspisV8.SelectedEarlyC1Amounts
