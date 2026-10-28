import NDE_VariantResults
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_ScalarResult
open NDE_VariantBridge

theorem scalar_lanes (v : V) (present : Bool) (input output privateTerm withdrawalTerm : Q) :
    NDE_LiftBridge.mapResult (fun a => a.val.map toNative)
      (NDE_Reference3.scalar_ref (isWithdrawal v) present input output privateTerm withdrawalTerm) =
    NDE_LiftBridge.mapResult (fun a => a.val)
      (FIq_Native.pool_v1.pair_forest_semantic_terminal.scalar_lanes v present
        (toNative input) (toNative output) (toNative privateTerm) (toNative withdrawalTerm)) := by
  cases v <;> cases present <;>
    simp only [NDE_Reference3.scalar_ref, isWithdrawal,
      FIq_Native.pool_v1.pair_forest_semantic_terminal.scalar_lanes,
      Bool.false_eq_true, ite_false, ite_true, bind_tc_ok,
      ← add_reference, NDE_RawBridge.map_bind]
  all_goals first
    | rfl
    | (cases NDE_Reference3.add_ref output privateTerm <;> rfl)
    | (cases NDE_Reference3.add_ref output withdrawalTerm <;> rfl)

#print axioms scalar_lanes
end NDE_ScalarResult
