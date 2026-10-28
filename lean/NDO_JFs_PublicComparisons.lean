import NDO_JFs_PublicValue
set_option autoImplicit false
namespace AspisR1.JFs_PublicComparisons
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JFs_PaymentValue.common.pool JFs_PublicValue.common.master_account=ok false := by rfl

theorem domain : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JFs_PaymentValue.common.deployment_domain
    JFs_PublicValue.common.lane_transition.live_snapshot.deployment_domain=ok false := by rfl

theorem snapshot_pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JFs_PublicValue.common.lane_transition.live_snapshot.pool
    JFs_PublicValue.common.master_account=ok false := by rfl

theorem anchor : core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31
    JFs_PaymentValue.common.anchor_root JFs_PublicValue.common.historical_global_anchor=ok false := by rfl

theorem sequence : (JFs_PaymentValue.common.anchor_sequence !=JFs_PublicValue.common.checkpoint_sequence)=false := by rfl

theorem lane_bound : ¬(core.convert.num.FromUsizeU8.from JFs_PublicValue.common.output_lane >=
    pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT) := by
  unfold pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
    core.convert.num.FromUsizeU8.from
  change ¬(UScalar.cast .Usize 3#u8 >=8#usize)
  scalar_tac

theorem lane : (3#u8 !=JFs_PublicValue.common.output_lane)=false := by rfl

#print axioms pool
#print axioms domain
#print axioms snapshot_pool
#print axioms anchor
#print axioms sequence
#print axioms lane_bound
#print axioms lane
end AspisR1.JFs_PublicComparisons
