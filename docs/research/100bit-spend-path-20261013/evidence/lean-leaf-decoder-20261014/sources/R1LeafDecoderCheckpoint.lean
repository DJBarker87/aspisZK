import R1MixedLeafDecoder
import R1FixedWidthDecodedSlices
import AeneasWordCodec

/-! Combined audits for strict field/leaf decoder composition and byte-word reuse.
No current Rust source refinement or full security claim is made. -/
set_option autoImplicit false

#print axioms AspisR1.FixedWidthSlice.flatMap_slice
#print axioms AspisR1.FixedWidthSlice.ofFn_flatMap_slice
#print axioms AspisR1.FixedWidthReconstruction.slices_flatten
#print axioms AspisR1.MixedLeafSlices.c1Slot_take_words
#print axioms AspisR1.MixedLeafSlices.c1Slot_drop_words
#print axioms AspisR1.MixedLeafSlices.c1Slot_m31_slice
#print axioms AspisR1.MixedLeafSlices.c1_slot_slice
#print axioms AspisR1.MixedLeafSlices.c2_slot_slice
#print axioms AspisR1.FixedWidthDecoder.decode_encode
#print axioms AspisR1.FixedWidthDecoder.encode_of_decode
#print axioms AspisR1.MixedLeafDecoder.decodeC1Slot_encode
#print axioms AspisR1.MixedLeafDecoder.encodeC1Slot_of_decode
#print axioms AspisR1.MixedLeafDecoder.decodeC2Slot_encode
#print axioms AspisR1.MixedLeafDecoder.encodeC2Slot_of_decode
#print axioms AspisR1.MixedLeafDecoder.decodeC1_encode
#print axioms AspisR1.MixedLeafDecoder.encodeC1_of_decode
#print axioms AspisR1.MixedLeafDecoder.decodeC2_encode
#print axioms AspisR1.MixedLeafDecoder.encodeC2_of_decode
#print axioms AspisR1.MixedLeafDecoder.decodeC1_eq_some_iff
#print axioms AspisR1.MixedLeafDecoder.decodeC2_eq_some_iff
#print axioms AspisR1.MixedLeafDecoder.decodeC1_length
#print axioms AspisR1.MixedLeafDecoder.decodeC2_length
#print axioms AspisR1.FixedWidthDecodedSlices.decode_eq_some_iff
#print axioms AspisR1.AeneasWordCodec.aeneasWord_val_eq
