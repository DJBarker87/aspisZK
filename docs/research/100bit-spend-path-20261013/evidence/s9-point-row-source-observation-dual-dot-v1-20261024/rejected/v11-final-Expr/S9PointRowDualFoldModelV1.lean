import S9PointRowTwoFoldV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9PointRowDualFoldModelV1
open AspisR1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
open AspisR1S9ScalarConstructorModelV1 (factorPolynomial)
/-- The actual source-buffer field observation vector is kept fixed. Its
constructor-model rowValue equals the model's precise two-fold dual dot.
This transports the optimized point-part expression, not an independently
chosen coefficient/input vector. -/
theorem rowValue_eq_two_dual_dot (model : Table) (k : Nat) (a0 a1 : E) (f : Slice U8) :
    rowValue model a0 a1 f k=
      RoundPairing.dot (fun i : Fin 64 => fieldValue f (finIndex AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1 i))
        (RoundPairing.dualFold a1
          (RoundPairing.dualFold a0 (fun j => embedQ (rawRow model k j)))) := by
  have hd := AspisR1S9SymbolicRowTransportV1.dot_scaled_transport
    (fun i : Fin 64 => fieldValue f (finIndex AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1 i))
    (fun i : Fin 64 => embedQ (highProduct (model k) i.val))
    (RoundPairing.dualFold a1
      (RoundPairing.dualFold a0 (fun j => embedQ (rawRow model k j))))
    (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))
    (fun i => (point_row_two_dual_folds model k a0 a1 i).trans
      (AspisR1S9PointNativeMulProjectionV1.native_mul_projected _ _))
  have hs := AspisR1S9PointExactOperatorTransportV1.scaled_sum_operator_eq
    (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))
    (fun i : Fin 64 => fieldValue f (finIndex AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1 i))
    (fun i : Fin 64 => embedQ (highProduct (model k) i.val))
  dsimp only [AspisR1S9PointExactOperatorTransportV1.fieldScaledSum] at hs
  run_tac Lean.Elab.Tactic.withMainContext do
    for n in [`hs,`hd] do
      let h ← Lean.Meta.getLocalDeclFromUserName n
      let ty ← Lean.instantiateMVars h.type
      let g ← Lean.Elab.Tactic.getMainGoal
      Lean.Elab.Tactic.replaceMainGoal [← g.replaceLocalDeclDefEq h.fvarId ty]
  delta AspisR1S9PointExactOperatorTransportV1.E
    AspisR1S9ScalarConstructorModelV1.E AspisR1S9SharedSumObservationsV1.E
    AspisR1S9SharedScalarModelValuesV1.E at hs hd
  have hc := hs.trans hd.symm
  unfold rowValue
  try (delta AspisR1S9PointExactOperatorTransportV1.E AspisR1S9ScalarConstructorModelV1.E AspisR1S9SharedSumObservationsV1.E AspisR1S9SharedScalarModelValuesV1.E at ⊢)
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Meta.getLocalDeclFromUserName `hc
    let a ← Lean.instantiateMVars h.type
    let g ← Lean.Elab.Tactic.getMainTarget
    let g ← Lean.instantiateMVars g
    Lean.logInfo s!"ACTUAL_EXPR {repr a}"
    Lean.logInfo s!"EXPECTED_EXPR {repr g}"
  exact hc

#print axioms rowValue_eq_two_dual_dot
end AspisR1S9PointRowDualFoldModelV1
