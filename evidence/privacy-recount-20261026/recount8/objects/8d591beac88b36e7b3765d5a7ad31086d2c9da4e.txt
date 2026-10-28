import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace R1Z.PV_RJDec_SnapshotRoot
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem rejection (s : PoolV1PairLiveSnapshotV1) (capacity : U64)
    (hp : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok false)
    (hd : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8) = ok false)
    (hs : (s.sequence != s.next_pair_index) = false)
    (hc : pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY = ok capacity)
    (hi : (s.next_pair_index >= capacity) = false)
    (bad : pool_v1.pair_tree_profile.digest_is_canonical s.current_root = ok false) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (.Err PoolV1PairLiveSnapshotErrorV1.NonCanonicalDigest) := by
  unfold validate_pool_v1_pair_live_snapshot_v1
  simp only [hp, hd, hs, hc, hi, bad, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]

#print axioms rejection
end R1Z.PV_RJDec_SnapshotRoot
