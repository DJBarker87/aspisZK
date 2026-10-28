import NDE_Reference5.Funs
import NDE_VariantResults
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_LinkBridge
abbrev Link := FIq_Native.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestLink
abbrev Variant := FIq_Native.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1

def isWithdrawal : Variant → Bool
  | .PrivateTransfer => false | .Withdrawal => true

theorem ok_right {α : Type} (r : Result α) : (r >>= Result.ok) = r := by
  cases r <;> rfl

theorem link_weight (link : Link) (index : U64) (v : Variant) :
    NDE_Reference5.link_weight_ref link.weight_kind link.weight_level index (isWithdrawal v) =
    FIq_Native.pool_v1.pair_forest_copy_terminal.link_weight link index v := by
  cases v <;> dsimp only [isWithdrawal]
  all_goals
    unfold NDE_Reference5.link_weight_ref FIq_Native.pool_v1.pair_forest_copy_terminal.link_weight
    split
    all_goals first
      | (simp_all [FIq_Native.field.M31.ONE, ok_right, lift] <;> rfl)
      | rfl

#print axioms ok_right
#print axioms link_weight
end NDE_LinkBridge
