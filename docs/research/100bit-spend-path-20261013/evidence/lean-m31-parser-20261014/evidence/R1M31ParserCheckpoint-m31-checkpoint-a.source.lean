import R1M31ParserArray

/-! Focused final import/axioms checkpoint for the retained current M31
parser and its exact canonical decoding contract, including its old reusable
byte and word arithmetic. This does not certify the extraction toolchain. -/

#print axioms AspisR1M31Parser.field.P
#print axioms AspisR1M31Parser.field.M31.from_le_bytes
#print axioms AspisR1M31Parser.parse_m31_probe
#print axioms AspisV8R19.SqueezeOracleBridge.word_roundtrip
#print axioms AspisR1.AeneasWordCodec.aeneasWord_val_eq
#print axioms AspisR1.M31ParserRefinement.from_le_bytes_refines
#print axioms AspisR1.M31ParserCanonicality.accepted_iff
#print axioms AspisR1.M31ParserCanonicality.rejected_iff
#print axioms AspisR1.M31ParserCanonicality.successful_value_canonical
#print axioms AspisR1.M31ParserArray.wordArray_arrayBytes
#print axioms AspisR1.M31ParserArray.parser_refines_array
#print axioms AspisR1.M31ParserArray.successful_array_value_canonical
