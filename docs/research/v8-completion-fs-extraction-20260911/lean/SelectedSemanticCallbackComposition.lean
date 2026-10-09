import SelectedCopyResidualCallback
import SelectedSourceTerminalAssembly

/-! Source-shaped composition of the selected semantic callback.

This leaf plugs the certified literal 136-link Copy evaluator and active-mask
evaluator into the complete 4+24+1 lane Horner polynomial, equality factor,
quadratic helper term, and final linear hiding expression.  Poseidon and the
24 packed semantic lanes are evaluated here as the MLEs of their independently
defined Boolean residual tables.  The Boolean restriction theorem therefore
identifies the entire assembled callback with the selected recovery table.

Still open are literal Rust/Aeneas refinement of the Poseidon, `semantic_packed`,
helper/H/G, and hiding-mask evaluators.  In particular, this file does not take
an equality between a caller-supplied callback and the source model as a
premise, but neither does it claim those remaining machine refinements. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AspisV8Completion.SelectedSemanticCallbackComposition
open AspisV5ComponentCQM31TowerExact
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList
open AspisV8.SelectedSemanticTransfer
open AspisV8.EarlyC1LateProjection
open AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedWeightedCopyCore
open AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedSemanticTerminalAlternative
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedConcreteRowLanes
open AspisV8Completion.SelectedCopyActiveFlat
open AspisV8Completion.SelectedCopyActiveExecutable
open AspisV8Completion.SelectedCopyResidualCallback
open AspisV8Completion.SelectedSourceTerminalAssembly

abbrev K := QM31Exact

/-- Mathematical MLE evaluator for the four selected Poseidon residual packs. -/
def poseidonMLE (rc : RoundConstants) (candidate : C1InitialMessages)
    (point : Fin 10 → K) (group : Fin 4) : K :=
  tableMLEValue point (fun row =>
    packedPoseidon rc (semanticTable candidate) row group)

/-- Mathematical MLE evaluator for the selected 95-position semantic table.
The 24th pack includes the separately specified positive-transfer slot. -/
def semanticMLE (pub : Public) (candidate : C1InitialMessages)
    (point : Fin 10 → K) (group : Fin 24) : K :=
  tableMLEValue point (fun row =>
    packedRows pub (semanticTable candidate) row group)

/-- All 29 callback lanes at one off-domain point.  The Copy lane is not a
free scalar: it is computed from the certified literal endpoints, patterns,
tags, weights and active-mask evaluator. -/
noncomputable def callbackLanes (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi helperAtPoint : K)
    (point : Fin 10 → K) : RowLanes K where
  poseidon := poseidonMLE rc candidate point
  semantic := semanticMLE pub candidate point
  copy := rustCopyTerminal (memberTable candidate) lambda .transfer
    pub.appendIndex point helperAtPoint chi

theorem selectedMLERow_boolean (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (row : Fin 1024) :
    selectedMLERow table lambda variant appendIndex (booleanTracePoint row) =
      sourceRows table lambda variant appendIndex row := by
  apply row_extensionality <;> funext slot
  · exact ((selectedMLERow_fields_are_sourceMLE table lambda variant appendIndex
      (booleanTracePoint row)).1 slot).trans (tableMLEValue_booleanTracePoint _ _)
  · exact ((selectedMLERow_fields_are_sourceMLE table lambda variant appendIndex
      (booleanTracePoint row)).2.1 slot).trans (tableMLEValue_booleanTracePoint _ _)
  · exact ((selectedMLERow_fields_are_sourceMLE table lambda variant appendIndex
      (booleanTracePoint row)).2.2.1 slot).trans (tableMLEValue_booleanTracePoint _ _)
  · exact ((selectedMLERow_fields_are_sourceMLE table lambda variant appendIndex
      (booleanTracePoint row)).2.2.2 slot).trans (tableMLEValue_booleanTracePoint _ _)

/-- At Boolean rows, the complete literal Copy functional is exactly the
selected nonlinear Copy residual table, including the active mask. -/
theorem rustCopyTerminal_boolean (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (helper : Fin 1024 → K)
    (chi : K) (row : Fin 1024) :
    rustCopyTerminal table lambda variant appendIndex (booleanTracePoint row)
        (helper row) chi =
      selectedBooleanResidual (sourceRows table lambda variant appendIndex)
        helper chi row := by
  rw [rustCopyTerminal_eq_selectedCopyTerminal]
  unfold selectedCopyTerminal selectedBooleanResidual
  rw [tableMLEValue_booleanTracePoint, selectedMLERow_boolean]
  rfl

theorem rowLanes_extensionality (left right : RowLanes K)
    (poseidon : left.poseidon = right.poseidon)
    (semantic : left.semantic = right.semantic)
    (copy : left.copy = right.copy) : left = right := by
  rcases left with ⟨leftPoseidon, leftSemantic, leftCopy⟩
  rcases right with ⟨rightPoseidon, rightSemantic, rightCopy⟩
  change leftPoseidon = rightPoseidon at poseidon
  change leftSemantic = rightSemantic at semantic
  change leftCopy = rightCopy at copy
  subst rightPoseidon
  subst rightSemantic
  subst rightCopy
  rfl

/-- The exact Boolean residual tables underlying the source-shaped evaluator.
This spelling avoids unfolding the larger payment candidate while proving the
off-domain evaluator's restriction theorem. -/
def booleanCallbackLanes (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi : K)
    (helper : Fin 1024 → K) (row : Fin 1024) : RowLanes K where
  poseidon := packedPoseidon rc (semanticTable candidate) row
  semantic := packedRows pub (semanticTable candidate) row
  copy := selectedBooleanResidual
    (sourceRows (memberTable candidate) lambda .transfer pub.appendIndex)
    helper chi row

theorem booleanCallbackLanes_eq_selected (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi : K)
    (helper : Fin 1024 → K) (row : Fin 1024) :
    booleanCallbackLanes rc pub candidate lambda chi helper row =
      lanes rc pub candidate lambda chi helper row := by
  rfl

/-- The assembled source-shaped lanes restrict to their exact selected
Boolean residual tables. -/
theorem callbackLanes_boolean (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi : K)
    (helper : Fin 1024 → K) (row : Fin 1024) :
    callbackLanes rc pub candidate lambda chi (helper row)
        (booleanTracePoint row) =
      booleanCallbackLanes rc pub candidate lambda chi helper row := by
  have poseidon :
      (callbackLanes rc pub candidate lambda chi (helper row)
        (booleanTracePoint row)).poseidon =
      (booleanCallbackLanes rc pub candidate lambda chi helper row).poseidon := by
    funext group
    change poseidonMLE rc candidate (booleanTracePoint row) group =
      packedPoseidon rc (semanticTable candidate) row group
    unfold poseidonMLE
    exact tableMLEValue_booleanTracePoint
      (fun selected => packedPoseidon rc (semanticTable candidate) selected group) row
  have semantic :
      (callbackLanes rc pub candidate lambda chi (helper row)
        (booleanTracePoint row)).semantic =
      (booleanCallbackLanes rc pub candidate lambda chi helper row).semantic := by
    funext group
    change semanticMLE pub candidate (booleanTracePoint row) group =
      packedRows pub (semanticTable candidate) row group
    unfold semanticMLE
    exact tableMLEValue_booleanTracePoint
      (fun selected => packedRows pub (semanticTable candidate) selected group) row
  have copy :
      (callbackLanes rc pub candidate lambda chi (helper row)
        (booleanTracePoint row)).copy =
      (booleanCallbackLanes rc pub candidate lambda chi helper row).copy := by
    exact rustCopyTerminal_boolean (memberTable candidate) lambda .transfer
      pub.appendIndex helper chi row
  exact rowLanes_extensionality _ _ poseidon semantic copy

/-- Complete unmasked callback assembly at an arbitrary point.  Each lane is
constructed above; there is no supplied callback-equality premise. -/
noncomputable def sourceCallbackOriginal (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint point : Fin 10 → K) (helperAtPoint mu : K) : K :=
  sourceOriginal
    (callbackLanes rc pub candidate lambda chi helperAtPoint point)
    helperAtPoint (rustSelectedCopyActive point) theta zerocheckPoint point mu

/-- The complete source-shaped callback polynomial is the degree-28 selected
lane polynomial inside the equality/helper assembly. -/
theorem sourceCallbackOriginal_eq_polynomial (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint point : Fin 10 → K) (helperAtPoint mu : K) :
    sourceCallbackOriginal rc pub candidate lambda chi theta zerocheckPoint
        point helperAtPoint mu =
      sourceEqualityValue zerocheckPoint point *
          (rowPolynomial
            (callbackLanes rc pub candidate lambda chi helperAtPoint point)).eval theta +
        mu * helperAtPoint +
        mu ^ 2 * ((1 - rustSelectedCopyActive point) * helperAtPoint) := by
  unfold sourceCallbackOriginal sourceOriginal
  rw [sourceComposition_eq_rowPolynomial_eval]

/-- Boolean restriction of the entire unmasked callback, not merely an
individual lane, equals the exact selected recovery table. -/
theorem sourceCallbackOriginal_boolean (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint : Fin 10 → K) (helper : Fin 1024 → K)
    (mu : K) (row : Fin 1024) :
    sourceCallbackOriginal rc pub candidate lambda chi theta zerocheckPoint
        (booleanTracePoint row) (helper row) mu =
      realTable (booleanCallbackLanes rc pub candidate lambda chi helper) helper
        activeIndicator theta zerocheckPoint mu row := by
  unfold sourceCallbackOriginal
  rw [callbackLanes_boolean, rustSelectedCopyActive_eq_sourceActiveFlat,
    sourceActiveFlat_boolean]
  exact sourceOriginal_booleanRow_eq_realTable
    (booleanCallbackLanes rc pub candidate lambda chi helper) helper activeIndicator
    theta zerocheckPoint mu row

/-- Final hiding assembly around the source-shaped callback.  The mask value
is deliberately an explicit evaluator output until the literal selected
H/G/mask evaluator is refined. -/
noncomputable def sourceCallbackMasked (maskValue eta : K)
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (lambda chi theta : K) (zerocheckPoint point : Fin 10 → K)
    (helperAtPoint mu : K) : K :=
  sourceMaskedTerminal maskValue
    (sourceCallbackOriginal rc pub candidate lambda chi theta zerocheckPoint
      point helperAtPoint mu) eta

theorem sourceCallbackMasked_eq_complete_assembly (maskValue eta : K)
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (lambda chi theta : K) (zerocheckPoint point : Fin 10 → K)
    (helperAtPoint mu : K) :
    sourceCallbackMasked maskValue eta rc pub candidate lambda chi theta
        zerocheckPoint point helperAtPoint mu =
      maskValue + eta *
        (sourceEqualityValue zerocheckPoint point *
            (rowPolynomial
              (callbackLanes rc pub candidate lambda chi helperAtPoint point)).eval theta +
          mu * helperAtPoint +
          mu ^ 2 * ((1 - rustSelectedCopyActive point) * helperAtPoint)) := by
  unfold sourceCallbackMasked sourceMaskedTerminal
  rw [sourceCallbackOriginal_eq_polynomial]

#print axioms selectedMLERow_boolean
#print axioms rustCopyTerminal_boolean
#print axioms booleanCallbackLanes_eq_selected
#print axioms callbackLanes_boolean
#print axioms sourceCallbackOriginal_eq_polynomial
#print axioms sourceCallbackOriginal_boolean
#print axioms sourceCallbackMasked_eq_complete_assembly
end AspisV8Completion.SelectedSemanticCallbackComposition
