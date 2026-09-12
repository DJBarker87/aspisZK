import SelectedCorrectedSemanticCallbackComposition
import SelectedPoseidonAllRowsPacking

/-! Abstract/source callback composition with both nonlinear lane families
evaluated by their chronological source expressions.

This replaces the two Boolean-table MLE shortcuts used by the older research
composition.  It proves the exact Boolean restriction and the existing
unmasked/masked terminal assembly identities.  The optimized mutable Rust
evaluator, helper/H/G evaluator, mask evaluator, and Aeneas refinement remain
external interfaces; no off-domain equality to the old MLEs is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3000

namespace AspisV8Completion.SelectedSourceSemanticPoseidonCallbackComposition
open AspisV5ComponentCQM31TowerExact
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList AspisPool.V7PairForestCuArithmeticEquivalences
open AspisV8.SelectedSemanticTransfer
open AspisV8.EarlyC1LateProjection AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedCopyAliases AspisV8.SelectedCopyAliasQM31
open AspisV8.SelectedCopyLayout AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedWeightedCopyCore AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticTerminalAlternative
open AspisV8.SelectedConcreteRowLanes
open AspisV8Completion.SelectedCopyActiveFlat
open AspisV8Completion.SelectedCopyActiveExecutable
open AspisV8Completion.SelectedCopyResidualCallback
open AspisV8Completion.SelectedSourceTerminalAssembly
open AspisV8Completion.SelectedSemanticCallbackComposition
open AspisV8Completion.SelectedCompleteSemanticPackedSource
open AspisV8Completion.SelectedPoseidonAllRowsPacking

abbrev K := QM31Exact

/-- The exact abstract source lanes.  Neither nonlinear family is evaluated
as the MLE of an already-computed Boolean residual table. -/
noncomputable def sourceSemanticPoseidonLanes (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi helperAtPoint : K)
    (point : Fin 10 → K) : RowLanes K where
  poseidon := sourcePoseidonLane rc (semanticTable candidate) point
  semantic := sourceSemanticField pub candidate point
  copy := rustCopyTerminal (memberTable candidate) lambda .transfer
    pub.appendIndex point helperAtPoint chi

theorem sourceSemanticPoseidonLanes_boolean (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi : K)
    (helper : Fin 1024 → K) (row : Fin 1024) :
    sourceSemanticPoseidonLanes rc pub candidate lambda chi (helper row)
        (booleanTracePoint row) =
      booleanCallbackLanes rc pub candidate lambda chi helper row := by
  have poseidonEq :
      sourcePoseidonLane rc (semanticTable candidate) (booleanTracePoint row) =
        packedPoseidon rc (semanticTable candidate) row := by
    funext group
    exact sourcePoseidonLane_boolean rc (semanticTable candidate) row group
  have semanticEq :
      sourceSemanticField pub candidate (booleanTracePoint row) =
        packedRows pub (semanticTable candidate) row := by
    funext group
    exact sourceSemanticLanes_boolean pub (semanticTable candidate) row group
  have copyEq :
      rustCopyTerminal (memberTable candidate) lambda .transfer pub.appendIndex
          (booleanTracePoint row) (helper row) chi =
        selectedBooleanResidual
          (sourceRows (memberTable candidate) lambda .transfer pub.appendIndex)
          helper chi row :=
    rustCopyTerminal_boolean (memberTable candidate) lambda .transfer
      pub.appendIndex helper chi row
  unfold sourceSemanticPoseidonLanes booleanCallbackLanes
  rw [poseidonEq, semanticEq, copyEq]

noncomputable def sourceSemanticPoseidonOriginal (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint point : Fin 10 → K) (helperAtPoint mu : K) : K :=
  sourceOriginal
    (sourceSemanticPoseidonLanes rc pub candidate lambda chi helperAtPoint point)
    helperAtPoint (rustSelectedCopyActive point) theta zerocheckPoint point mu

theorem sourceSemanticPoseidonOriginal_eq_polynomial (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint point : Fin 10 → K) (helperAtPoint mu : K) :
    sourceSemanticPoseidonOriginal rc pub candidate lambda chi theta zerocheckPoint
        point helperAtPoint mu =
      sourceEqualityValue zerocheckPoint point *
          (rowPolynomial
            (sourceSemanticPoseidonLanes rc pub candidate lambda chi helperAtPoint point)).eval
              theta +
        mu * helperAtPoint +
        mu ^ 2 * ((1 - rustSelectedCopyActive point) * helperAtPoint) := by
  unfold sourceSemanticPoseidonOriginal sourceOriginal
  rw [sourceComposition_eq_rowPolynomial_eval]

theorem sourceSemanticPoseidonOriginal_boolean (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi theta : K)
    (zerocheckPoint : Fin 10 → K) (helper : Fin 1024 → K)
    (mu : K) (row : Fin 1024) :
    sourceSemanticPoseidonOriginal rc pub candidate lambda chi theta zerocheckPoint
        (booleanTracePoint row) (helper row) mu =
      realTable (booleanCallbackLanes rc pub candidate lambda chi helper) helper
        activeIndicator theta zerocheckPoint mu row := by
  unfold sourceSemanticPoseidonOriginal
  rw [sourceSemanticPoseidonLanes_boolean,
    rustSelectedCopyActive_eq_sourceActiveFlat, sourceActiveFlat_boolean]
  exact sourceOriginal_booleanRow_eq_realTable
    (booleanCallbackLanes rc pub candidate lambda chi helper) helper activeIndicator
    theta zerocheckPoint mu row

noncomputable def sourceSemanticPoseidonMasked (maskValue eta : K)
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (lambda chi theta : K) (zerocheckPoint point : Fin 10 → K)
    (helperAtPoint mu : K) : K :=
  sourceMaskedTerminal maskValue
    (sourceSemanticPoseidonOriginal rc pub candidate lambda chi theta zerocheckPoint
      point helperAtPoint mu) eta

theorem sourceSemanticPoseidonMasked_eq_assembly (maskValue eta : K)
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (lambda chi theta : K) (zerocheckPoint point : Fin 10 → K)
    (helperAtPoint mu : K) :
    sourceSemanticPoseidonMasked maskValue eta rc pub candidate lambda chi theta
        zerocheckPoint point helperAtPoint mu =
      maskValue + eta *
        (sourceEqualityValue zerocheckPoint point *
            (rowPolynomial
              (sourceSemanticPoseidonLanes rc pub candidate lambda chi helperAtPoint point)).eval
                theta +
          mu * helperAtPoint +
          mu ^ 2 * ((1 - rustSelectedCopyActive point) * helperAtPoint)) := by
  unfold sourceSemanticPoseidonMasked sourceMaskedTerminal
  rw [sourceSemanticPoseidonOriginal_eq_polynomial]

#print axioms sourceSemanticPoseidonLanes_boolean
#print axioms sourceSemanticPoseidonOriginal_eq_polynomial
#print axioms sourceSemanticPoseidonOriginal_boolean
#print axioms sourceSemanticPoseidonMasked_eq_assembly
end AspisV8Completion.SelectedSourceSemanticPoseidonCallbackComposition
