import S6AfterstateDecoderFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Frames
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

theorem frame_prepend (bytes : Slice U8) (root digest : Digest) (prior : List Digest)
    (afterstate : PoolV1PairVerifiedAfterstateV1)
    (later : part_frame bytes root (prior++[digest]) afterstate)
    (current : digest_frame bytes (48+32*prior.length) digest) :
    part_frame bytes root prior afterstate := by
  rcases later with ⟨hroot, suffix, hfrontier, hframes, hindex, hvalidate⟩
  refine ⟨hroot, digest::suffix, ?_, ⟨current, ?_⟩, hindex, hvalidate⟩
  · simpa only [List.append_assoc, List.singleton_append] using hfrontier
  · simpa [List.length_append, Nat.mul_add, Nat.add_assoc] using hframes

#print axioms frame_prepend
end AspisS6SourceCodec.AfterstateFactored.Frames
