import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailChunkProjectionCompose
open Aeneas Aeneas.Std

theorem compose_chunk_projection
    (tail : Array U8 768#usize) (digest : Array U8 32#usize)
    (bytes : Array U8 4#usize) (base offset : Nat)
    (hoff : offset + 4 ≤ 32)
    (htail : ∀ j : Nat, j < 32 → tail.val[base + j]? = digest.val[j]?)
    (hchunk : ∀ k : Nat, k < 4 → digest.val[offset + k]? = bytes.val[k]?) :
    ∀ k : Nat, k < 4 → tail.val[base + (offset + k)]? = bytes.val[k]? := by
  intro k hk
  rw [htail (offset + k) (by omega)]
  exact hchunk k hk

#print axioms compose_chunk_projection
end AspisR1PairForestLaneEncoderTailChunkProjectionCompose
