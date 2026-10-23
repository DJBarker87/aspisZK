import S6SourceAfterstateDecodeTotalV1
import S6ByteInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Frames
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal
abbrev Digest := Array U32 8#usize

def digest_frame (bytes : Slice U8) (offset : Nat) (digest : Digest) : Prop :=
  ∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical digest=ok encoded ∧
    encoded.val=List.slice offset (offset+32) bytes.val

def frontier_frames (bytes : Slice U8) : Nat → List Digest → Prop
  | _, [] => True
  | offset, digest::tail => digest_frame bytes offset digest ∧ frontier_frames bytes (offset+32) tail

def part_frame (bytes : Slice U8) (root : Digest) (prior : List Digest)
    (afterstate : PoolV1PairVerifiedAfterstateV1) : Prop :=
  afterstate.next_root=root ∧ ∃ suffix,
    afterstate.next_frontier.val=prior++suffix ∧
    frontier_frames bytes (48+32*prior.length) suffix ∧
    (core.num.U64.to_le_bytes afterstate.next_pair_index).val=List.slice 8 16 bytes.val ∧
    validate_verified_afterstate afterstate=ok (core.result.Result.Ok ())

@[step] theorem part16_frames (bytes : Slice U8)
    (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Digest)
    (hlen : bytes.length=688) :
    part_16 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
      ⦃ result => ∀ afterstate, result=core.result.Result.Ok afterstate →
        part_frame bytes val1 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23,val25,val27,val29,val31,val33] afterstate ⦄ := by
  unfold part_16
  step*
  all_goals (intro afterstate accepted; cases accepted)
  all_goals (unfold part_frame; refine ⟨rfl, [val35,val37,val39,val41], rfl, ?_, ?_, ?_⟩)
  all_goals (simp_all [frontier_frames,digest_frame,AspisS6ByteInverse.u64_to_from,List.slice])

#print axioms part16_frames
end AspisS6SourceCodec.AfterstateFactored.Frames
