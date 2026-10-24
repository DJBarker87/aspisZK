import S9PointRowDualFoldModelV1
import S9StoredRowsCommonInputV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9PointCommonInputFoldV1
open AspisR1
open AspisR1S9FactorTableSemanticsV1 (Table)
open AspisR1S9PointRowDualFoldModelV1 (E rawRow)
open AspisR1S9SharedScalarModelValuesV1 (embedQ)
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
open AspisR1S9StoredRowsCommonInputV1 (commonInput)

def pointFoldValue (model : Table) (a0 a1 : E) (f : Slice U8) (row : Nat) : E :=
  RoundPairing.dot
    (commonInput f AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1)
    (RoundPairing.dualFold a1
      (RoundPairing.dualFold a0 (fun j => embedQ (rawRow model row j))))

theorem rowValue_eq_common_input_fold (model : Table) (a0 a1 : E)
    (f : Slice U8) (row : Nat) :
    rowValue model a0 a1 f row=pointFoldValue model a0 a1 f row := by
  have h := AspisR1S9PointRowDualFoldModelV1.rowValue_eq_two_dual_dot model row a0 a1 f
  dsimp only [pointFoldValue,commonInput]
  run_tac Lean.Elab.Tactic.withMainContext do
    let hd ← Lean.Meta.getLocalDeclFromUserName `h
    let ty ← Lean.instantiateMVars hd.type
    let g ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.Tactic.replaceMainGoal [← g.replaceLocalDeclDefEq hd.fvarId ty]
  try (delta E AspisR1S9StoredRowsCommonInputV1.E AspisR1S9SharedSumObservationsV1.E AspisR1S9SharedScalarModelValuesV1.E at h)
  try (delta E AspisR1S9StoredRowsCommonInputV1.E AspisR1S9SharedSumObservationsV1.E AspisR1S9SharedScalarModelValuesV1.E at ⊢)
  exact h
#print axioms rowValue_eq_common_input_fold
end AspisR1S9PointCommonInputFoldV1
end
