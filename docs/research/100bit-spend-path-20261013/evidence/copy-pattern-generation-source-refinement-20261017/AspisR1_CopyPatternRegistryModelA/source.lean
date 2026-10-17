import AspisR1.CopyPatternRegistryModel10

/-! Small descriptor-data checks. The exceptional offset record is proved first
in CopyPatternRegistryModel10. No field expression is normalized. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternRegistryModel
noncomputable section
open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact

theorem raw0_columns : ∀ j : Fin 16, (cell (rawAt 0).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw0_offsets : ∀ j : Fin 16,
    (cell (rawAt 0).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw0_model : modelPattern (rawAt 0) raw0_columns = R0P.copyPattern0 := by
  unfold modelPattern R0P.copyPattern0
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw0_columns
#print axioms raw0_offsets
#print axioms raw0_model

theorem raw1_columns : ∀ j : Fin 16, (cell (rawAt 1).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw1_offsets : ∀ j : Fin 16,
    (cell (rawAt 1).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw1_model : modelPattern (rawAt 1) raw1_columns = R0P.copyPattern1 := by
  unfold modelPattern R0P.copyPattern1
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw1_columns
#print axioms raw1_offsets
#print axioms raw1_model

theorem raw2_columns : ∀ j : Fin 16, (cell (rawAt 2).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw2_offsets : ∀ j : Fin 16,
    (cell (rawAt 2).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw2_model : modelPattern (rawAt 2) raw2_columns = R0P.copyPattern2 := by
  unfold modelPattern R0P.copyPattern2
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw2_columns
#print axioms raw2_offsets
#print axioms raw2_model

theorem raw3_columns : ∀ j : Fin 16, (cell (rawAt 3).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw3_offsets : ∀ j : Fin 16,
    (cell (rawAt 3).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw3_model : modelPattern (rawAt 3) raw3_columns = R0P.copyPattern3 := by
  unfold modelPattern R0P.copyPattern3
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw3_columns
#print axioms raw3_offsets
#print axioms raw3_model

theorem raw4_columns : ∀ j : Fin 16, (cell (rawAt 4).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw4_offsets : ∀ j : Fin 16,
    (cell (rawAt 4).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw4_model : modelPattern (rawAt 4) raw4_columns = R0P.copyPattern4 := by
  unfold modelPattern R0P.copyPattern4
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw4_columns
#print axioms raw4_offsets
#print axioms raw4_model

theorem raw5_columns : ∀ j : Fin 16, (cell (rawAt 5).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw5_offsets : ∀ j : Fin 16,
    (cell (rawAt 5).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw5_model : modelPattern (rawAt 5) raw5_columns = R0P.copyPattern5 := by
  unfold modelPattern R0P.copyPattern5
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw5_columns
#print axioms raw5_offsets
#print axioms raw5_model

end
end AspisR1.CopyPatternRegistryModel
