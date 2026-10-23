import S6SliceFrameContentsV1
set_option autoImplicit false
namespace AspisS6SliceFrame
/-- Eight symbolic writes of four bytes fill a 32-byte buffer exactly.
No concrete byte values or field operations are unfolded. -/
theorem eight_chunks {T : Type} (zero : T)
    (w0 w1 w2 w3 w4 w5 w6 w7 : List T)
    (h0 : w0.length=4)
    (h1 : w1.length=4)
    (h2 : w2.length=4)
    (h3 : w3.length=4)
    (h4 : w4.length=4)
    (h5 : w5.length=4)
    (h6 : w6.length=4)
    (h7 : w7.length=4) :
    (((((((((List.replicate 32 zero).setSlice! 0 w0).setSlice! 4 w1).setSlice! 8 w2).setSlice! 12 w3).setSlice! 16 w4).setSlice! 20 w5).setSlice! 24 w6).setSlice! 28 w7) =
      w0++w1++w2++w3++w4++w5++w6++w7 := by
  have step0 : (List.replicate 32 zero).setSlice! 0 w0 =
      ([]++w0)++List.replicate 28 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0] using
      (setSlice_append_chunk [] w0 32 zero (by rw [h0]; decide))
  have step1 : ((w0)++List.replicate 28 zero).setSlice! 4 w1 =
      ((w0)++w1)++List.replicate 24 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0, h1] using
      (setSlice_append_chunk (w0) w1 28 zero (by rw [h1]; decide))
  have step2 : ((w0++w1)++List.replicate 24 zero).setSlice! 8 w2 =
      ((w0++w1)++w2)++List.replicate 20 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2] using
      (setSlice_append_chunk (w0++w1) w2 24 zero (by rw [h2]; decide))
  have step3 : ((w0++w1++w2)++List.replicate 20 zero).setSlice! 12 w3 =
      ((w0++w1++w2)++w3)++List.replicate 16 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3] using
      (setSlice_append_chunk (w0++w1++w2) w3 20 zero (by rw [h3]; decide))
  have step4 : ((w0++w1++w2++w3)++List.replicate 16 zero).setSlice! 16 w4 =
      ((w0++w1++w2++w3)++w4)++List.replicate 12 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3, h4] using
      (setSlice_append_chunk (w0++w1++w2++w3) w4 16 zero (by rw [h4]; decide))
  have step5 : ((w0++w1++w2++w3++w4)++List.replicate 12 zero).setSlice! 20 w5 =
      ((w0++w1++w2++w3++w4)++w5)++List.replicate 8 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3, h4, h5] using
      (setSlice_append_chunk (w0++w1++w2++w3++w4) w5 12 zero (by rw [h5]; decide))
  have step6 : ((w0++w1++w2++w3++w4++w5)++List.replicate 8 zero).setSlice! 24 w6 =
      ((w0++w1++w2++w3++w4++w5)++w6)++List.replicate 4 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3, h4, h5, h6] using
      (setSlice_append_chunk (w0++w1++w2++w3++w4++w5) w6 8 zero (by rw [h6]; decide))
  have step7 : ((w0++w1++w2++w3++w4++w5++w6)++List.replicate 4 zero).setSlice! 28 w7 =
      ((w0++w1++w2++w3++w4++w5++w6)++w7)++List.replicate 0 zero := by
    simpa only [List.length_append, List.length_nil, List.nil_append, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2, h3, h4, h5, h6, h7] using
      (setSlice_append_chunk (w0++w1++w2++w3++w4++w5++w6) w7 4 zero (by rw [h7]; decide))
  simp only [step0, List.nil_append]
  rw [step1]
  rw [step2]
  rw [step3]
  rw [step4]
  rw [step5]
  rw [step6]
  rw [step7]
  simp only [List.replicate_zero,List.append_nil,List.append_assoc]

#print axioms eight_chunks
end AspisS6SliceFrame
