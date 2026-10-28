import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace R1Z.PV_RJDec_SnapshotDomain
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem rejection (s : PoolV1PairLiveSnapshotV1)
    (hp : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok false)
    (bad : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8) = ok true) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (.Err PoolV1PairLiveSnapshotErrorV1.ZeroRequiredBinding) := by
  unfold validate_pool_v1_pair_live_snapshot_v1
  simp only [hp, bad, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]

#print axioms rejection
end R1Z.PV_RJDec_SnapshotDomain
