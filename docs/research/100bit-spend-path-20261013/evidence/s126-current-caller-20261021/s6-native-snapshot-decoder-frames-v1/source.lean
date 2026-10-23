import S6NativeSnapshotDecodeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
abbrev Digest := Array U32 8#usize

def chunk_frames (bytes : Slice U8) : Nat → List Digest → Prop
  | _, [] => True
  | offset, digest::tail =>
    AspisS6SourceCodec.DigestContents.chunks digest=List.slice offset (offset+32) bytes.val ∧
      chunk_frames bytes (offset+32) tail

def part_frame (bytes : Slice U8) (root : Digest) (prior : List Digest)
    (snapshot : PoolV1PairLiveSnapshotV1) : Prop :=
  snapshot.current_root=root ∧ ∃ suffix,
    snapshot.frontier.val=prior++suffix ∧ chunk_frames bytes (160+32*prior.length) suffix ∧
    snapshot.pool.val=List.slice 48 80 bytes.val ∧
    snapshot.deployment_domain.val=List.slice 80 112 bytes.val ∧
    (core.num.U64.to_le_bytes snapshot.sequence).val=List.slice 112 120 bytes.val ∧
    (core.num.U64.to_le_bytes snapshot.next_pair_index).val=List.slice 120 128 bytes.val ∧
    validate_pool_v1_pair_live_snapshot_v1 snapshot=ok (core.result.Result.Ok ())

@[step] theorem part16_frames (bytes : Slice U8)
    (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Digest)
    (size : bytes.length=800) :
    part_16 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16
      ⦃ result => ∀ snapshot, result=core.result.Result.Ok snapshot →
        part_frame bytes val [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10,val11,val12,val13,val14,val15,val16] snapshot ⦄ := by
  unfold part_16
  step*
  all_goals (intro snapshot accepted; cases accepted)
  all_goals (unfold part_frame; refine ⟨rfl,[val17,val18,val19,val20],rfl,?_,?_,?_,?_,?_,?_⟩)
  all_goals (simp_all [chunk_frames,AspisS6ByteInverse.u64_to_from,List.slice])

#print axioms part16_frames
end AspisS6NativeSnapshotDecoderFactored.Frames
