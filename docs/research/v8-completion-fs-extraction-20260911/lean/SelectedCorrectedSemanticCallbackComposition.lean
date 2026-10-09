import SelectedCompleteSemanticPackedSource

/-! Semantic-lane source-polynomial substitution inside the callback shape.

The old research composition used `semanticMLE`, the multilinear extension
of the Boolean residual table, at off-domain points.  This sibling uses the
actual nonlinear source-polynomial values for those 24 lanes.  Poseidon,
Copy, helper, active indicator, equality factor and hiding assembly are
otherwise unchanged.

In particular, `poseidonMLE` is still the MLE of packed Boolean Poseidon
residuals.  The literal callback evaluates nonlinear Poseidon formulas from
off-domain openings, so Poseidon needs its own chronological source-polynomial
bridge before this shape can be called the complete corrected callback.
The carried image gate belongs to the later relation callback and is not
redefined here.

No equality with the old callback away from Boolean rows and no literal
Rust/Aeneas refinement is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3000

namespace AspisV8Completion.SelectedSemanticLaneCorrectedComposition
open AspisV5ComponentCQM31TowerExact
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList
open AspisV8.SelectedSemanticTransfer
open AspisV8.EarlyC1LateProjection
open AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedCopyAliases
open AspisV8.SelectedCopyAliasQM31
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedWeightedCopyCore
open AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticTerminalAlternative
open AspisV8.SelectedConcreteRowLanes
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedCopyActiveFlat
open AspisV8Completion.SelectedCopyActiveExecutable
open AspisV8Completion.SelectedCopyResidualCallback
open AspisV8Completion.SelectedSourceTerminalAssembly
open AspisV8Completion.SelectedSemanticCallbackComposition
open AspisV8Completion.SelectedCompleteSemanticSourcePolynomial
open AspisV8Completion.SelectedCompleteSemanticPackedSource

abbrev K := QM31Exact

/-- The corrected 29-lane object.  Only the semantic field changes from the
older research callback, and it changes to the actual source-polynomial
evaluation rather than a Boolean-table MLE. -/
noncomputable def semanticLaneReplacedLanes (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi helperAtPoint : K)
    (point : Fin 10 → K) : RowLanes K where
  poseidon := poseidonMLE rc candidate point
  semantic := sourceSemanticField pub candidate point
  copy := rustCopyTerminal (memberTable candidate) lambda .transfer
    pub.appendIndex point helperAtPoint chi

/-- Each coordinate message is genuinely degree at most 27 because it is the
message of the corresponding constructed chronological source polynomial. -/
theorem indexedSemanticMessage_degree (pub : Public) (table : BaseTable)
    (index : Fin 95) (point : Fin 10 → K) (round : Fin 10) :
    (sourceMessages (indexedSource pub table index) point round).natDegree ≤ 27 :=
  sourceMessages_degree (indexedSource pub table index) point round

/-- At Boolean rows the corrected lanes remain exactly the selected Boolean
recovery-table lanes.  This does not identify either evaluator off-domain. -/
theorem semanticLaneReplacedLanes_boolean (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi : K)
    (helper : Fin 1024 → K) (row : Fin 1024) :
    semanticLaneReplacedLanes rc pub candidate lambda chi (helper row)
        (booleanTracePoint row) =
      booleanCallbackLanes rc pub candidate lambda chi helper row := by
  have sameOld :
      semanticLaneReplacedLanes rc pub candidate lambda chi (helper row)
          (booleanTracePoint row) =
        callbackLanes rc pub candidate lambda chi (helper row)
          (booleanTracePoint row) := by
    apply rowLanes_extensionality
    · rfl
    · exact sourceSemanticField_boolean pub candidate row
    · rfl
  exact sameOld.trans (callbackLanes_boolean rc pub candidate lambda chi helper row)

noncomputable def semanticLaneReplacedSourceOriginal (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint point : Fin 10 → K) (helperAtPoint mu : K) : K :=
  sourceOriginal
    (semanticLaneReplacedLanes rc pub candidate lambda chi helperAtPoint point)
    helperAtPoint (rustSelectedCopyActive point) theta zerocheckPoint point mu

theorem semanticLaneReplacedSourceOriginal_eq_polynomial (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint point : Fin 10 → K) (helperAtPoint mu : K) :
    semanticLaneReplacedSourceOriginal rc pub candidate lambda chi theta zerocheckPoint
        point helperAtPoint mu =
      sourceEqualityValue zerocheckPoint point *
          (rowPolynomial
            (semanticLaneReplacedLanes rc pub candidate lambda chi helperAtPoint point)).eval
              theta +
        mu * helperAtPoint +
        mu ^ 2 * ((1 - rustSelectedCopyActive point) * helperAtPoint) := by
  unfold semanticLaneReplacedSourceOriginal sourceOriginal
  rw [sourceComposition_eq_rowPolynomial_eval]

theorem semanticLaneReplacedSourceOriginal_boolean (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint : Fin 10 → K) (helper : Fin 1024 → K)
    (mu : K) (row : Fin 1024) :
    semanticLaneReplacedSourceOriginal rc pub candidate lambda chi theta zerocheckPoint
        (booleanTracePoint row) (helper row) mu =
      realTable (booleanCallbackLanes rc pub candidate lambda chi helper) helper
        activeIndicator theta zerocheckPoint mu row := by
  unfold semanticLaneReplacedSourceOriginal
  rw [semanticLaneReplacedLanes_boolean, rustSelectedCopyActive_eq_sourceActiveFlat,
    sourceActiveFlat_boolean]
  exact sourceOriginal_booleanRow_eq_realTable
    (booleanCallbackLanes rc pub candidate lambda chi helper) helper activeIndicator
    theta zerocheckPoint mu row

noncomputable def semanticLaneReplacedSourceMasked (maskValue eta : K)
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (lambda chi theta : K) (zerocheckPoint point : Fin 10 → K)
    (helperAtPoint mu : K) : K :=
  sourceMaskedTerminal maskValue
    (semanticLaneReplacedSourceOriginal rc pub candidate lambda chi theta zerocheckPoint
      point helperAtPoint mu) eta

theorem semanticLaneReplacedSourceMasked_eq_assembly (maskValue eta : K)
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (lambda chi theta : K) (zerocheckPoint point : Fin 10 → K)
    (helperAtPoint mu : K) :
    semanticLaneReplacedSourceMasked maskValue eta rc pub candidate lambda chi theta
        zerocheckPoint point helperAtPoint mu =
      maskValue + eta *
        (sourceEqualityValue zerocheckPoint point *
            (rowPolynomial
              (semanticLaneReplacedLanes rc pub candidate lambda chi helperAtPoint point)).eval
                theta +
          mu * helperAtPoint +
          mu ^ 2 * ((1 - rustSelectedCopyActive point) * helperAtPoint)) := by
  unfold semanticLaneReplacedSourceMasked sourceMaskedTerminal
  rw [semanticLaneReplacedSourceOriginal_eq_polynomial]

#print axioms semanticLaneReplacedLanes
#print axioms indexedSemanticMessage_degree
#print axioms semanticLaneReplacedLanes_boolean
#print axioms semanticLaneReplacedSourceOriginal_boolean
#print axioms semanticLaneReplacedSourceMasked_eq_assembly
end AspisV8Completion.SelectedSemanticLaneCorrectedComposition
