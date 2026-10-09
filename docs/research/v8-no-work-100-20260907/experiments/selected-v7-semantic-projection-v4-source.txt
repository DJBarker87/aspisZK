import AspisFormal.Pool.V7AtomicSemanticRowsFromTrace
import SelectedEarlyC1Inputs
import SelectedEarlyC1Outputs

/-! Source-review replacement of the failed numerical-index glue: project only the portions of the V7 atomic77
Boolean-row model whose cells/equations match selected pair-forest95.
No equality of independently supplied traces, selected acceptance, or
valid-witness premise is used. The changed selectors, Poseidon expressions,
amount/occupancy and public fields remain explicit source obligations.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedV7SemanticProjection
open Polynomial Finset
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisPool.V7AtomicSemanticRowsFromTrace AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7ExtractedLaneWords AspisPool.V7FixedWidth29TupleList
open AspisPool.V7Width29ComponentExtraction
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact AspisV5ProductionPublicResidualBinding
open AspisV8.EarlyC1LateProjection AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedEarlyC1Amounts AspisV8.SelectedEarlyC1Inputs
open AspisV8.SelectedEarlyC1Outputs AspisV8.SelectedNoteRecovery
open AspisV8.SelectedOutputNotes
noncomputable section

/-- Literal finite restriction of the same selected table, not a supplied
trace witness or an equality to an independently chosen honest trace. -/
def physical (candidate : C1InitialMessages) : PhysicalTrace :=
  fun row column => semanticTable candidate row.val column.val

theorem physical_tuple_eq (components : Width29InitialMessages QM31Exact) :
    physical (c1Projection components) = semanticTrace components := by
  funext row column
  rw [physical, semanticTable_read, memberTable_read]
  rfl

/-- Narrow port of V7HashBlocksFromTrace.initialResidual_at_retainedInitialRow.
It depends only on the atomic row model, not the old copy/trace closure. -/
theorem initial_residual_retained (trace : PhysicalTrace) (which : Fin 4)
    (column : Fin 16) :
    initialResidual trace (retainedInitialRow which) column =
      trace (retainedInitialRow which) column - initialExpected which column := by
  have retainedEqual : ∀ other : Fin 4,
      retainedInitialRow which = retainedInitialRow other ↔ other = which := by
    intro other
    constructor
    · intro equal
      apply Fin.ext
      have values := congrArg Fin.val equal
      fin_cases which <;> fin_cases other <;>
        simp [retainedInitialRow] at values ⊢
    · intro equal
      subst other
      rfl
  have noPath : ∀ block : Fin 40,
      retainedInitialRow which ≠ pathInitialRow block := by
    intro block equal
    have values := congrArg Fin.val equal
    fin_cases which <;>
      simp [retainedInitialRow, pathInitialRow] at values <;> omega
  simp [initialResidual, retainedEqual, noPath]

/-- Pointwise form of the V7 retained-initial-state theorem; no Poseidon
state wrapper/import is needed to reuse its proof. -/
theorem retained_initial_exact (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) (which : Fin 4) (column : Fin 16) :
    trace (retainedInitialRow which) column =
      initState (retainedInitialDomain which) (retainedInitialLength which) column := by
  have residual := coordinate_residual_zero_of_semantic_rows_vanish
    fields trace vanish (.initial column) (retainedInitialRow which)
  rw [atomicSemanticResidual, initial_residual_retained trace which column] at residual
  rw [sub_eq_zero.mp residual]
  unfold initialExpected initState
  have eight : column = (8 : Fin 16) ↔ column.val = 8 := Fin.ext_iff
  have nine : column = (9 : Fin 16) ↔ column.val = 9 := Fin.ext_iff
  simp only [eight, nine]

/-- Narrow port of V7HashBlocksFromTrace's low absorption padding theorem. -/
theorem low_padding_zero (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) (which : Fin 2) (column : Fin 16)
    (padding : 2 ≤ column.val) (rate : column.val < 8) :
    trace (absorptionLowRow which) column = 0 := by
  have residual := coordinate_residual_zero_of_semantic_rows_vanish
    fields trace vanish (.absorption column) (absorptionLowRow which)
  change absorptionResidual trace (absorptionLowRow which) column = 0 at residual
  have notHigh : ¬8 ≤ column.val := by omega
  fin_cases which <;>
    simp [absorptionResidual, absorptionLowRow, padding, rate, notHigh] at residual ⊢ <;>
    exact residual

/-- Narrow port of V7MerkleLevelFromTrace.initialResidual_at_pathInitialRow_low. -/
theorem initial_residual_path_low (trace : PhysicalTrace) (block : Fin 40)
    (column : Fin 16) (low : column.val < 8) :
    initialResidual trace (pathInitialRow block) column = trace (pathInitialRow block) column := by
  have noRetained : ∀ which : Fin 4,
      pathInitialRow block ≠ retainedInitialRow which := by
    intro which equal
    have values := congrArg Fin.val equal
    fin_cases which <;>
      simp [pathInitialRow, retainedInitialRow] at values <;> omega
  have pathEqual : ∀ other : Fin 40,
      pathInitialRow block = pathInitialRow other ↔ other = block := by
    intro other
    constructor
    · intro equal
      apply Fin.ext
      have values := congrArg Fin.val equal
      simp [pathInitialRow] at values
      omega
    · intro equal
      subst other
      rfl
  simp [initialResidual, low, noRetained, pathEqual]

theorem path_initial_zero (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) (block : Fin 40)
    (column : Fin 16) (low : column.val < 8) :
    trace (pathInitialRow block) column = 0 := by
  have residual := coordinate_residual_zero_of_semantic_rows_vanish
    fields trace vanish (.initial column) (pathInitialRow block)
  rw [atomicSemanticResidual, initial_residual_path_low trace block column low] at residual
  exact residual

/-- Exactly62 scalar consequences at matching selected cells. These are
three complete input-check fields and the low halves of three initial states.
No range, occupancy, public-output, or Poseidon check is hidden in this record. -/
structure MatchingChecks (candidate : C1InitialMessages) : Prop where
  initialOwner : ∀ i : Fin 16, semanticTable candidate 0 i.val - initState DOM_OWNER 8 i = 0
  initialNote : ∀ i : Fin 16, semanticTable candidate 16 i.val - initState DOM_NOTE 18 i = 0
  noteTailZero : ∀ i : Fin 6, semanticTable candidate 60 (i.val + 2) = 0
  nullifierLow : ∀ i : Fin 16, i.val < 8 → semanticTable candidate 400 i.val = 0
  outputLow : ∀ which : Fin 2, ∀ i : Fin 16, i.val < 8 →
    semanticTable candidate (16 * outputBlock which) i.val = 0

theorem matching_checks (fields : TerminalSpendFields) (candidate : C1InitialMessages)
    (vanish : AtomicSemanticRowsVanish fields (physical candidate)) : MatchingChecks candidate := by
  constructor
  · intro i
    have exactState := retained_initial_exact fields (physical candidate) vanish
      (⟨0, by decide⟩ : Fin 4) i
    apply sub_eq_zero.mpr
    simpa [physical, retainedInitialRow, retainedInitialDomain,
      retainedInitialLength, DOM_OWNER] using exactState
  · intro i
    have exactState := retained_initial_exact fields (physical candidate) vanish
      (⟨1, by decide⟩ : Fin 4) i
    apply sub_eq_zero.mpr
    simpa [physical, retainedInitialRow, retainedInitialDomain,
      retainedInitialLength, DOM_NOTE] using exactState
  · intro i
    let column : Fin 16 := ⟨i.val + 2, by omega⟩
    have padding : 2 ≤ column.val := by dsimp only [column]; omega
    have rate : column.val < 8 := by dsimp only [column]; omega
    have zero := low_padding_zero fields (physical candidate) vanish
      (⟨0, by decide⟩ : Fin 2) column padding rate
    change semanticTable candidate 60 (i.val + 2) = 0 at zero
    exact zero
  · intro i low
    have zero := path_initial_zero fields (physical candidate) vanish
      (⟨21, by decide⟩ : Fin 40) i low
    change semanticTable candidate 400 i.val = 0 at zero
    exact zero
  · intro which i low
    fin_cases which
    · change semanticTable candidate 432 i.val = 0
      have zero := path_initial_zero fields (physical candidate) vanish
        (⟨23, by decide⟩ : Fin 40) i low
      change semanticTable candidate 432 i.val = 0 at zero
      exact zero
    · change semanticTable candidate 480 i.val = 0
      have zero := path_initial_zero fields (physical candidate) vanish
        (⟨26, by decide⟩ : Fin 40) i low
      change semanticTable candidate 480 i.val = 0 at zero
      exact zero

/-- The actual selected Poseidon expressions and the moved nullifier
capacity half have no counterpart in the old atomic semantic77 oracle. -/
structure RemainingInputChecks (rc : RoundConstants) (candidate : C1InitialMessages) : Prop where
  pairs : ∀ block, block ∈ activeBlocks → BlockResiduals rc (semanticTable candidate) block
  nullifierCapacity : ∀ i : Fin 16, 8 ≤ i.val →
    semanticTable candidate 400 i.val - initState DOM_NULLIFIER 16 i = 0

/-- Both selected output capacity halves and both moved padding supports
remain explicit, as do the independent Poseidon round-pair expressions. -/
structure RemainingOutputChecks (rc : RoundConstants) (candidate : C1InitialMessages) : Prop where
  pairs : ∀ which : Fin 2, ∀ j : Fin 3,
    BlockResiduals rc (semanticTable candidate) (outputBlock which + j.val)
  capacity : ∀ which : Fin 2, ∀ i : Fin 16, 8 ≤ i.val →
    semanticTable candidate (16 * outputBlock which) i.val - initState DOM_NOTE 18 i = 0
  tailZero : ∀ which : Fin 2, ∀ i : Fin 6,
    semanticTable candidate (16 * (outputBlock which + 2) + 12) (i.val + 2) = 0

theorem input_checks_from_atomic (rc : RoundConstants) (fields : TerminalSpendFields)
    (candidate : C1InitialMessages)
    (vanish : AtomicSemanticRowsVanish fields (physical candidate))
    (remaining : RemainingInputChecks rc candidate) : InputSemanticChecks rc candidate := by
  have matched := matching_checks fields candidate vanish
  refine ⟨remaining.pairs, matched.initialOwner, matched.initialNote, ?_, matched.noteTailZero⟩
  intro i
  by_cases low : i.val < 8
  · have notEight : i.val ≠ 8 := by omega
    have notNine : i.val ≠ 9 := by omega
    simp only [initState, if_neg notEight, if_neg notNine, sub_zero]
    exact matched.nullifierLow i low
  · exact remaining.nullifierCapacity i (by omega)

theorem output_checks_from_atomic (rc : RoundConstants) (fields : TerminalSpendFields)
    (candidate : C1InitialMessages)
    (vanish : AtomicSemanticRowsVanish fields (physical candidate))
    (remaining : RemainingOutputChecks rc candidate) : OutputSemanticChecks rc candidate := by
  have matched := matching_checks fields candidate vanish
  refine ⟨remaining.pairs, ?_, remaining.tailZero⟩
  intro which i
  by_cases low : i.val < 8
  · have notEight : i.val ≠ 8 := by omega
    have notNine : i.val ≠ 9 := by omega
    simp only [initState, if_neg notEight, if_neg notNine, sub_zero]
    exact matched.outputLow which i low
  · exact remaining.capacity which i (by omega)

/-- Maximal matching-field projection, not selected verifier acceptance.
AmountSemanticChecks, InputPairSemanticChecks and selected public residuals
are intentionally absent from the conclusion: their layouts do not match. -/
theorem semantic_projection (rc : RoundConstants) (fields : TerminalSpendFields)
    (candidate : C1InitialMessages)
    (vanish : AtomicSemanticRowsVanish fields (physical candidate))
    (input : RemainingInputChecks rc candidate)
    (output : RemainingOutputChecks rc candidate) :
    InputSemanticChecks rc candidate ∧ OutputSemanticChecks rc candidate :=
  ⟨input_checks_from_atomic rc fields candidate vanish input,
    output_checks_from_atomic rc fields candidate vanish output⟩

#print axioms physical_tuple_eq
#print axioms initial_residual_retained
#print axioms retained_initial_exact
#print axioms low_padding_zero
#print axioms initial_residual_path_low
#print axioms path_initial_zero
#print axioms matching_checks
#print axioms input_checks_from_atomic
#print axioms output_checks_from_atomic
#print axioms semantic_projection
end
end AspisV8.SelectedV7SemanticProjection
