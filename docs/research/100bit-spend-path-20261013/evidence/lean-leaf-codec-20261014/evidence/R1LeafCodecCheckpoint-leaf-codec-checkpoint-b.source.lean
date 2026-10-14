import R1MixedLeafEncoding

/-! Combined audit of retained field codecs and current mixed leaf encodings.
These model identities do not establish current Rust parser correspondence. -/

#print axioms AspisR1.FixedWidthEncoding.flatMap_injective
#print axioms AspisR1.FixedWidthEncoding.ofFn_flatMap_injective
#print axioms AspisR1.RetainedFieldByteCodec.decodeWordLE_encodeWordLE
#print axioms AspisR1.RetainedFieldByteCodec.decodeM31LE_encodeM31LE
#print axioms AspisR1.RetainedFieldByteCodec.decodeQM31LE_encodeQM31LE
#print axioms AspisR1.RetainedFieldByteCodec.encodeWordLE_decodeWordLE
#print axioms AspisR1.RetainedFieldByteCodec.encodeQM31LE_of_decodeQM31LE
#print axioms AspisR1.RetainedFieldByteCodec.decodeQM31Bytes
#print axioms AspisR1.ListFieldCodec.fixedBytes?_ofFn
#print axioms AspisR1.ListFieldCodec.fixedBytes?_sound
#print axioms AspisR1.ListFieldCodec.decodeM31Bytes_encode
#print axioms AspisR1.ListFieldCodec.encodeM31Bytes_of_decode
#print axioms AspisR1.ListFieldCodec.decodeQM31Bytes_encode
#print axioms AspisR1.ListFieldCodec.encodeQM31Bytes_of_decode
#print axioms AspisR1.RetainedExactLimbCodec.qm31ExactToLimbs_limbsToQM31Exact
#print axioms AspisR1.RetainedExactLimbCodec.limbsToQM31Exact_qm31ExactToLimbs
#print axioms AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv_apply
#print axioms AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv_symm_apply
#print axioms AspisR1.ExactLeafFieldCodec.encodeM31_length
#print axioms AspisR1.ExactLeafFieldCodec.decodeM31_encodeM31
#print axioms AspisR1.ExactLeafFieldCodec.encodeM31_of_decodeM31
#print axioms AspisR1.ExactLeafFieldCodec.encodeM31_injective
#print axioms AspisR1.ExactLeafFieldCodec.encodeQM31_length
#print axioms AspisR1.ExactLeafFieldCodec.decodeQM31_encodeQM31
#print axioms AspisR1.ExactLeafFieldCodec.encodeQM31_of_decodeQM31
#print axioms AspisR1.ExactLeafFieldCodec.encodeQM31_injective
#print axioms AspisR1.MixedLeafEncoding.encodeC1Slot_length
#print axioms AspisR1.MixedLeafEncoding.encodeC2Slot_length
#print axioms AspisR1.MixedLeafEncoding.encodeC1_length
#print axioms AspisR1.MixedLeafEncoding.encodeC2_length
#print axioms AspisR1.MixedLeafEncoding.encodeC1Slot_injective
#print axioms AspisR1.MixedLeafEncoding.encodeC2Slot_injective
#print axioms AspisR1.MixedLeafEncoding.encodeC1_injective
#print axioms AspisR1.MixedLeafEncoding.encodeC2_injective
