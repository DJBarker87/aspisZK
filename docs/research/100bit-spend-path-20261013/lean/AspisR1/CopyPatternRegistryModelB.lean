import AspisR1.CopyPatternRegistryModel10

/-! Small descriptor-data checks. The exceptional offset record is proved first
in CopyPatternRegistryModel10. No field expression is normalized. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternRegistryModel
noncomputable section
open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact

theorem raw6_columns : ∀ j : Fin 16, (cell (rawAt 6).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw6_offsets : ∀ j : Fin 16,
    (cell (rawAt 6).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw6_model : modelPattern (rawAt 6) raw6_columns = R0P.copyPattern6 := by
  unfold modelPattern R0P.copyPattern6
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw6_columns
#print axioms raw6_offsets
#print axioms raw6_model

theorem raw7_columns : ∀ j : Fin 16, (cell (rawAt 7).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw7_offsets : ∀ j : Fin 16,
    (cell (rawAt 7).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw7_model : modelPattern (rawAt 7) raw7_columns = R0P.copyPattern7 := by
  unfold modelPattern R0P.copyPattern7
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw7_columns
#print axioms raw7_offsets
#print axioms raw7_model

theorem raw8_columns : ∀ j : Fin 16, (cell (rawAt 8).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw8_offsets : ∀ j : Fin 16,
    (cell (rawAt 8).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw8_model : modelPattern (rawAt 8) raw8_columns = R0P.copyPattern8 := by
  unfold modelPattern R0P.copyPattern8
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw8_columns
#print axioms raw8_offsets
#print axioms raw8_model

theorem raw9_columns : ∀ j : Fin 16, (cell (rawAt 9).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw9_offsets : ∀ j : Fin 16,
    (cell (rawAt 9).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw9_model : modelPattern (rawAt 9) raw9_columns = R0P.copyPattern9 := by
  unfold modelPattern R0P.copyPattern9
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw9_columns
#print axioms raw9_offsets
#print axioms raw9_model

theorem raw11_columns : ∀ j : Fin 16, (cell (rawAt 11).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw11_offsets : ∀ j : Fin 16,
    (cell (rawAt 11).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw11_model : modelPattern (rawAt 11) raw11_columns = R0P.copyPattern11 := by
  unfold modelPattern R0P.copyPattern11
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw11_columns
#print axioms raw11_offsets
#print axioms raw11_model

theorem raw12_columns : ∀ j : Fin 16, (cell (rawAt 12).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw12_offsets : ∀ j : Fin 16,
    (cell (rawAt 12).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw12_model : modelPattern (rawAt 12) raw12_columns = R0P.copyPattern12 := by
  unfold modelPattern R0P.copyPattern12
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw12_columns
#print axioms raw12_offsets
#print axioms raw12_model

theorem raw13_columns : ∀ j : Fin 16, (cell (rawAt 13).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw13_offsets : ∀ j : Fin 16,
    (cell (rawAt 13).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw13_model : modelPattern (rawAt 13) raw13_columns = R0P.copyPattern13 := by
  unfold modelPattern R0P.copyPattern13
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw13_columns
#print axioms raw13_offsets
#print axioms raw13_model

end
end AspisR1.CopyPatternRegistryModel
