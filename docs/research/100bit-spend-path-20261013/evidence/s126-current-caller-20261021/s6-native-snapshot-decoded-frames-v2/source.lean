import S6NativeSnapshotDecoderPart0FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def header_frame (raw : Array U8 800#usize) : Prop :=
  List.slice 0 8 raw.val=POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val ∧
  raw.val[8]'(by rw [raw.property]; decide)=POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION ∧
  raw.val[9]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[10]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[11]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[12]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[13]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[14]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[15]'(by rw [raw.property]; decide)=0#u8 ∧
  ∃ format : Array U8 32#usize, POOL_V1_PAIR_TREE_FORMAT_BINDING=ok format ∧
    format.val=List.slice 16 48 raw.val

def full_frame (bytes : Slice U8) (snapshot : PoolV1PairLiveSnapshotV1) : Prop :=
  (∃ raw : Array U8 800#usize, raw.val=bytes.val ∧ header_frame raw) ∧
  AspisS6SourceCodec.DigestContents.chunks snapshot.current_root=List.slice 128 160 bytes.val ∧
  chunk_frames bytes 160 snapshot.frontier.val ∧
  snapshot.pool.val=List.slice 48 80 bytes.val ∧
  snapshot.deployment_domain.val=List.slice 80 112 bytes.val ∧
  (core.num.U64.to_le_bytes snapshot.sequence).val=List.slice 112 120 bytes.val ∧
  (core.num.U64.to_le_bytes snapshot.next_pair_index).val=List.slice 120 128 bytes.val ∧
  validate_pool_v1_pair_live_snapshot_v1 snapshot=ok (core.result.Result.Ok ())

@[step] theorem decode_frames (bytes : Slice U8) :
    decode bytes ⦃ result => ∀ snapshot,
      result=core.result.Result.Ok snapshot → full_frame bytes snapshot ⦄ := by
  unfold decode core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*
  all_goals trace_state

#print axioms decode_frames
end AspisS6NativeSnapshotDecoderFactored.Frames
