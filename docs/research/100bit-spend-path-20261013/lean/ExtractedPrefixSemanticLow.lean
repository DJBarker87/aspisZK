import StrictLowChunkCodec
import ExtractedPrefixStrictPayload

/-! Compatibility source-parser entrypoint. The unchanged shared low-chunk
codec and algebraic facts now live in StrictLowChunkCodec. The actual Prefix
strict-parse theorems remain available through ExtractedPrefixStrictPayload. -/

#print axioms AspisR1.ExtractedPrefixSemanticLow.pair_high_zero
#print axioms AspisR1.ExtractedPrefixSemanticLow.strict_chunk_decodeLow
