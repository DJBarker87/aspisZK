import S6PointWriteFrameV1
set_option autoImplicit false
namespace AspisS6SliceFrame
/-- Complete common payment write schedule, on symbolic chunks. -/
theorem payment_common_chunks {T : Type} (zero : T)
    (head pool deployment sequence anchor nullifier asset : List T)
    (h0 : head.length=8)
    (h1 : pool.length=32)
    (h2 : deployment.length=32)
    (h3 : sequence.length=8)
    (h4 : anchor.length=32)
    (h5 : nullifier.length=32)
    (h6 : asset.length=4) :
    (((((((head++List.replicate 208 zero).setSlice! 8 pool).setSlice! 40 deployment).setSlice! 72 sequence).setSlice! 80 anchor).setSlice! 112 nullifier).setSlice! 144 asset) =
      (head++pool++deployment++sequence++anchor++nullifier++asset)++List.replicate 68 zero := by
  have step1 : ((head)++List.replicate 208 zero).setSlice! 8 pool =
      ((head)++pool)++List.replicate 176 zero := by
    simpa only [List.length_append, Nat.reduceAdd, Nat.reduceSub, h0, h1] using
      (setSlice_append_chunk (head) pool 208 zero (by rw [h1]; decide))
  have step2 : ((head++pool)++List.replicate 176 zero).setSlice! 40 deployment =
      ((head++pool)++deployment)++List.replicate 144 zero := by
    simpa only [List.length_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2] using
      (setSlice_append_chunk (head++pool) deployment 176 zero (by rw [h2]; decide))
  have step3 : ((head++pool++deployment)++List.replicate 144 zero).setSlice! 72 sequence =
      ((head++pool++deployment)++sequence)++List.replicate 136 zero := by
    simpa only [List.length_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3] using
      (setSlice_append_chunk (head++pool++deployment) sequence 144 zero (by rw [h3]; decide))
  have step4 : ((head++pool++deployment++sequence)++List.replicate 136 zero).setSlice! 80 anchor =
      ((head++pool++deployment++sequence)++anchor)++List.replicate 104 zero := by
    simpa only [List.length_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3, h4] using
      (setSlice_append_chunk (head++pool++deployment++sequence) anchor 136 zero (by rw [h4]; decide))
  have step5 : ((head++pool++deployment++sequence++anchor)++List.replicate 104 zero).setSlice! 112 nullifier =
      ((head++pool++deployment++sequence++anchor)++nullifier)++List.replicate 72 zero := by
    simpa only [List.length_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3, h4, h5] using
      (setSlice_append_chunk (head++pool++deployment++sequence++anchor) nullifier 104 zero (by rw [h5]; decide))
  have step6 : ((head++pool++deployment++sequence++anchor++nullifier)++List.replicate 72 zero).setSlice! 144 asset =
      ((head++pool++deployment++sequence++anchor++nullifier)++asset)++List.replicate 68 zero := by
    simpa only [List.length_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3, h4, h5, h6] using
      (setSlice_append_chunk (head++pool++deployment++sequence++anchor++nullifier) asset 72 zero (by rw [h6]; decide))
  rw [step1, step2, step3, step4, step5, step6]

#print axioms payment_common_chunks
end AspisS6SliceFrame
