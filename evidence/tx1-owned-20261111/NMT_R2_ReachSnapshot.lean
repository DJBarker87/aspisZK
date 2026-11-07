import NMT_345Decoder
set_option autoImplicit false
noncomputable section
namespace NMT_R2_Reach
open Aeneas Aeneas.Std
abbrev Snapshot := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev LateError := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
abbrev SnapshotCall := Slice U8 → Result (core.result.Result Snapshot LateError)

def snapshot : SnapshotCall :=
 AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1

/-- The first internal Box is reached exactly on this helper's Ok arm.
The marker is a pure control probe, never a runtime assumption or Kani oracle. -/
def markSnapshot (bytes : Slice U8) : Result (core.result.Result Snapshot LateError) := do
 let r ← snapshot bytes
 match r with
 | .Ok _ => .div
 | .Err e => .ok (.Err e)

theorem snapshot_total (bytes : Slice U8) : ∃ r, snapshot bytes = .ok r := by
 obtain ⟨r,hr⟩ := AspisS6NativeSnapshotDecodeTotal.decode_total bytes
 have source := congrArg (fun x => x.1) (NGF_NEX_SnapshotBoxOracle.result_state_effects bytes ())
 dsimp only at source
 unfold snapshot
 rw [← source]
 unfold NGF_NEX_SnapshotBoxOracle.run
 rw [hr]
 cases r <;> exact ⟨_,rfl⟩

theorem marker_iff (bytes : Slice U8) : markSnapshot bytes = .div ↔
 ∃ value, snapshot bytes = .ok (.Ok value) := by
 obtain ⟨r,hr⟩ := snapshot_total bytes
 unfold markSnapshot
 rw [hr]
 cases r with
 | Ok value => exact ⟨fun _ => ⟨value,rfl⟩,fun _ => rfl⟩
 | Err e => simp
#print axioms snapshot_total
#print axioms marker_iff
end NMT_R2_Reach
end
