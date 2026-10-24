import S6SourceAfterstateAcceptedFramesV1
import S6PaymentFrameRecomposeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Frames
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

theorem consecutive_slices {T : Type} (xs : List T) (start first second : Nat) :
    List.slice start (start+first) xs ++
      List.slice (start+first) (start+first+second) xs =
    List.slice start (start+first+second) xs := by
  simp only [List.slice, Nat.add_sub_cancel_left]
  rw [show start+first+second-start=first+second by omega]
  rw [←List.drop_drop, ←List.take_add]

theorem digest_frame_contents (bytes : Slice U8) (offset : Nat) (digest : Digest)
    (frame : digest_frame bytes offset digest) :
    DigestContents.chunks digest=List.slice offset (offset+32) bytes.val := by
  rcases frame with ⟨encoded, actual, contents⟩
  exact (PaymentContents.encoded_digest_chunks digest encoded actual).trans contents

theorem frontier_frame_contents (bytes : Slice U8) (offset : Nat) (digests : List Digest)
    (frames : frontier_frames bytes offset digests) :
    digests.flatMap DigestContents.chunks=List.slice offset (offset+32*digests.length) bytes.val := by
  induction digests generalizing offset with
  | nil => simp [List.slice]
  | cons digest tail ih =>
    rcases frames with ⟨head,rest⟩
    rw [List.flatMap_cons,digest_frame_contents bytes offset digest head,ih _ rest]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using consecutive_slices bytes.val offset 32 (32*tail.length)

#print axioms consecutive_slices
#print axioms digest_frame_contents
#print axioms frontier_frame_contents
end AspisS6SourceCodec.AfterstateFactored.Frames
