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
  cases v <;>
    simp only [NDE_Reference5.link_weight_ref,
      FIq_Native.pool_v1.pair_forest_copy_terminal.link_weight,
      FIq_Native.field.M31.ONE, isWithdrawal]
  all_goals split <;> first
    | rfl
    | (simp only [lift, bind_tc_ok]; rfl)
    | (cases index >>> link.weight_level <;> simp only [bind_tc_ok] <;>
        first | rfl | (rename_i z; cases 1#u32 - UScalar.cast .U32 (z &&& 1#u64) <;> rfl))

#print axioms link_weight
end NDE_LinkBridge
