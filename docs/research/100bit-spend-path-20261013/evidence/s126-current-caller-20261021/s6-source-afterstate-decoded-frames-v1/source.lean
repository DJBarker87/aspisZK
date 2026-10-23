import S6AfterstateDecoderPart0FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Frames
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

def header_frame (raw : Array U8 688#usize) : Prop :=
  List.slice 0 4 raw.val=POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val ∧
  raw.val[4]'(by rw [raw.property]; decide)=POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION ∧
  raw.val[5]'(by rw [raw.property]; decide)=aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION ∧
  raw.val[6]'(by rw [raw.property]; decide)=aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION ∧
  raw.val[7]'(by rw [raw.property]; decide)=1#u8

def full_frame (bytes : Slice U8) (afterstate : PoolV1PairVerifiedAfterstateV1) : Prop :=
  (∃ raw : Array U8 688#usize, raw.val=bytes.val ∧ header_frame raw) ∧
  digest_frame bytes 16 afterstate.next_root ∧
  frontier_frames bytes 48 afterstate.next_frontier.val ∧
  (core.num.U64.to_le_bytes afterstate.next_pair_index).val=List.slice 8 16 bytes.val ∧
  validate_verified_afterstate afterstate=ok (core.result.Result.Ok ())

@[step] theorem decode_frames (bytes : Slice U8) :
    decode bytes ⦃ result => ∀ afterstate,
      result=core.result.Result.Ok afterstate → full_frame bytes afterstate ⦄ := by
  unfold decode core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*
  all_goals (simp_all [full_frame,part_frame,digest_frame])

#print axioms decode_frames
end AspisS6SourceCodec.AfterstateFactored.Frames
