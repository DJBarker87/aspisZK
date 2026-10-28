import NDE_Reference5.Funs
import NDE_VariantResults
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_LinkBridge
abbrev Link := FIq_Native.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestLink
abbrev Variant := FIq_Native.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1

def isWithdrawal : Variant → Bool
  | .PrivateTransfer => false | .Withdrawal => true

theorem link_weight (link : Link) (index : U64) (v : Variant) :
    NDE_Reference5.link_weight_ref link.weight_kind link.weight_level index (isWithdrawal v) =
    FIq_Native.pool_v1.pair_forest_copy_terminal.link_weight link index v := by
  cases v <;> dsimp only [isWithdrawal]
  all_goals
    unfold NDE_Reference5.link_weight_ref FIq_Native.pool_v1.pair_forest_copy_terminal.link_weight
    split
    all_goals
      try simp only [FIq_Native.field.M31.ONE, lift, bind_tc_ok]
      first
      | rfl
      | (cases hs : index >>> link.weight_level <;> simp only [hs, bind_tc_ok, lift] <;>
          first | rfl | (rename_i z; cases 1#u32 - UScalar.cast .U32 (z &&& 1#u64) <;> rfl))

#print axioms link_weight
end NDE_LinkBridge
