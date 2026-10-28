import NDE_VariantBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_VariantResults
open NDE_VariantBridge

theorem initial_selectors (v : V) (a b c : Q) :
    NDE_LiftBridge.mapResult mapFour
      (NDE_Reference3.initial_ref (isWithdrawal v) a b c) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors v
      (toNative a) (toNative b) (toNative c) := by
  cases v <;>
    simp only [NDE_Reference3.initial_ref, NDE_Reference3.lift_ref,
      isWithdrawal, FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors,
      Bool.false_eq_true, ite_false, ite_true, bind_tc_ok,
      ← add_reference, NDE_RawBridge.map_bind]
  all_goals
    cases hab : NDE_Reference3.add_ref a b <;>
      simp [hab, NDE_LiftBridge.mapResult, mapFour,
        FIq_Native.field.QM31.ZERO, FIq_Native.field.CM31.ZERO, ← add_reference]

def nativeVariant (b : Bool) :
    FIq_Native.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1 :=
  if b then .Withdrawal else .PrivateTransfer

theorem copy_variant (v : V) :
    NDE_LiftBridge.mapResult nativeVariant
      (NDE_Reference3.copy_variant_ref (isWithdrawal v)) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.copy_variant v := by
  cases v <;> rfl

#print axioms initial_selectors
#print axioms copy_variant
end NDE_VariantResults
