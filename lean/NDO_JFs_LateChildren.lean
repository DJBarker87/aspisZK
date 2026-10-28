import NDO_JFs_AfterstateDecode
import NDO_JFt_SnapshotDecode
set_option autoImplicit false
namespace AspisR1.JFs_LateChildren
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def value : PoolV1PairLatePublicStatementV1 :=
  ⟨JFt_SnapshotValue.value,JFt_AfterstateValue.value⟩

theorem snapshot : decode_pair_live_snapshot_boxed_v1 JFu_PublicRange.snapshot=
    ok (.Ok JFt_SnapshotValue.value) := by
  unfold decode_pair_live_snapshot_boxed_v1
  rw [JFt_SnapshotDecode.source]
  rfl

theorem afterstate : decode_pair_afterstate_boxed_v1 JFu_PublicRange.afterstate=
    ok (.Ok JFt_AfterstateValue.value) := by
  unfold decode_pair_afterstate_boxed_v1
  rw [JFs_AfterstateDecode.source]
  rfl

theorem next : U64.checked_add JFt_SnapshotValue.value.next_pair_index 1#u64=
    some JFt_AfterstateValue.value.next_pair_index := by rfl

theorem next_compare : core.cmp.PartialEq.ne.trait_default
    (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
    (some JFt_AfterstateValue.value.next_pair_index)
    (some JFt_AfterstateValue.value.next_pair_index)=ok false := by rfl

#print axioms snapshot
#print axioms afterstate
#print axioms next
#print axioms next_compare
end AspisR1.JFs_LateChildren
