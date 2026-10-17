import AspisR1.CopyPatternLimbExact

/-! Focused exceptional-offset record check before the full registry bridge. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternRegistryModel
noncomputable section
open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact
abbrev Registry := AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS

def rawAt (index : Fin 14) : Pattern :=
  Registry.val[index.val]'(by simpa [Registry.property] using index.isLt)

theorem raw10_columns : ∀ j : Fin 16, (cell (rawAt 10).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw10_offsets : ∀ j : Fin 16,
    (cell (rawAt 10).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw10_model : modelPattern (rawAt 10) raw10_columns = R0P.copyPattern10 := by
  unfold modelPattern R0P.copyPattern10
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw10_columns
#print axioms raw10_offsets
#print axioms raw10_model
end
end AspisR1.CopyPatternRegistryModel
