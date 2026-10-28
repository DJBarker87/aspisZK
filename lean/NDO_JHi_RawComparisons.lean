import NDO_JHg_RawPrefix
import NDO_JFs_PublicComparisons
set_option autoImplicit false
namespace AspisR1.JHi_RawComparisons
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

theorem pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_RawPrefix.payment.pool JHg_RawCommon.common.master_account=ok false :=
  JFs_PublicComparisons.pool
#print axioms pool

theorem domain : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_RawPrefix.payment.deployment_domain
    JHg_RawCommon.common.lane_transition.live_snapshot.deployment_domain=ok false :=
  JFs_PublicComparisons.domain
#print axioms domain

theorem snapshot_pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_RawCommon.common.lane_transition.live_snapshot.pool
    JHg_RawCommon.common.master_account=ok false := JFs_PublicComparisons.snapshot_pool
#print axioms snapshot_pool

theorem anchor : core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31
    JHg_RawPrefix.payment.anchor_root JHg_RawCommon.common.historical_global_anchor=ok false :=
  JFs_PublicComparisons.anchor
#print axioms anchor

theorem sequence : (JHg_RawPrefix.payment.anchor_sequence !=JHg_RawCommon.common.checkpoint_sequence)=false :=
  JFs_PublicComparisons.sequence
#print axioms sequence

theorem lane_bound : ¬(core.convert.num.FromUsizeU8.from JHg_RawCommon.common.output_lane >=
    aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT) := by
  unfold aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
    core.convert.num.FromUsizeU8.from
  change ¬(UScalar.cast .Usize 3#u8 >=8#usize)
  scalar_tac
#print axioms lane_bound

theorem lane : (3#u8 !=JHg_RawCommon.common.output_lane)=false := JFs_PublicComparisons.lane
#print axioms lane
end AspisR1.JHi_RawComparisons
