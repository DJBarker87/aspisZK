import AspisR1PublicPreparation.Types

-- Identical source is checked against original and naming-only adapted Types.
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1PublicPreparation.DiscriminantAudit

def codes (a b : U8) (n : Usize)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (t : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (c : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : List Isize :=
  [read_discriminant (aspis_core.state_only_prefix.r0.Error.Allocation),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.RowOrder a b),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.InvalidRow),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.Tag a),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.Length a),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.NonCanonical a n),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.Boundary n),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.Terminal),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.EqualCirclePoints),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.TrailingBytes),
   read_discriminant (aspis_core.state_only_prefix.r0.Error.Public),
   read_discriminant (r1_wire.Error.Allocation),
   read_discriminant (r1_wire.Error.RowOrder a b),
   read_discriminant (r1_wire.Error.InvalidRow),
   read_discriminant (r1_wire.Error.Tag a),
   read_discriminant (r1_wire.Error.Length a),
   read_discriminant (r1_wire.Error.NonCanonical a n),
   read_discriminant (r1_wire.Error.Boundary n),
   read_discriminant (r1_wire.Error.Terminal),
   read_discriminant (r1_wire.Error.EqualCirclePoints),
   read_discriminant (r1_wire.Error.TrailingBytes),
   read_discriminant (r1_wire.Error.Public),
   read_discriminant (pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer),
   read_discriminant (pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal),
   read_discriminant (pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer p t),
   read_discriminant (pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal w t),
   read_discriminant (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer c p),
   read_discriminant (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal c w)]

theorem codes_eq (a b : U8) (n : Usize)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (t : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (c : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) :
    codes a b n p w t c =
      [0#isize, 1#isize, 2#isize, 3#isize, 4#isize, 5#isize, 6#isize, 7#isize, 8#isize, 9#isize, 10#isize, 0#isize, 1#isize, 2#isize, 3#isize, 4#isize, 5#isize, 6#isize, 7#isize, 8#isize, 9#isize, 10#isize, 0#isize, 1#isize, 0#isize, 1#isize, 0#isize, 1#isize] := rfl

#print axioms codes_eq
end AspisR1PublicPreparation.DiscriminantAudit
