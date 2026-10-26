import FIy_OccupancyMeaning
import FIw_SelectorRow
set_option autoImplicit false
namespace AspisR1.FIy_OccupancyRows
open Aeneas Aeneas.Std Result FIq_Native
abbrev Variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant

def expected (v : Variant) : Nat := match v with
  | .PrivateTransfer=>1
  | .Withdrawal=>0

theorem input : pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW=ok 1017#usize := by
  rw [pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW]
  scalar_tac

theorem output : pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW=ok 1018#usize := by
  rw [pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW]
  scalar_tac

theorem expected_value (v : Variant) (out : U32)
    (run : pool_v1.pair_forest_semantic_terminal.variant_expected_output v=ok out) :
    out.val<FIw_ScalarArithmetic.P ∧ out.val=expected v := by
  cases v <;> simp only [pool_v1.pair_forest_semantic_terminal.variant_expected_output] at run <;>
    cases Result.ok.inj run <;> exact ⟨by decide,rfl⟩
#print axioms input
#print axioms output
#print axioms expected_value
end AspisR1.FIy_OccupancyRows
