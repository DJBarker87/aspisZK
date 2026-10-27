import RPz7_S6NativeSnapshotDecoderFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem frame_prepend (bytes : Slice U8) (root digest : Digest) (prior : List Digest)
    (snapshot : PoolV1PairLiveSnapshotV1)
    (later : part_frame bytes root (prior++[digest]) snapshot)
    (current : AspisS6SourceCodec.DigestContents.chunks digest =
      List.slice (160+32*prior.length) (160+32*prior.length+32) bytes.val) :
    part_frame bytes root prior snapshot := by
  rcases later with ⟨hroot, suffix, hfrontier, hframes, hpool, hdomain, hseq, hindex, hvalidate⟩
  refine ⟨hroot, digest::suffix, ?_, ⟨current, ?_⟩, hpool, hdomain, hseq, hindex, hvalidate⟩
  · simpa only [List.append_assoc, List.singleton_append] using hfrontier
  · simpa [List.length_append, Nat.mul_add, Nat.add_assoc] using hframes

#print axioms frame_prepend
end AspisS6NativeSnapshotDecoderFactored.Frames
