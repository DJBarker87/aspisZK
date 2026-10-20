# Original serializer and strict parser roundtrip

For a source WideExact whose eight U32 coordinates are below P, the unchanged emitted serializer under the corrected P6 iterator model succeeds, the extracted strict parser accepts its exact output bytes, and all eight parsed coordinate values equal the original source coordinates. The proof reuses the checked original serializer output, explicit carrier bridge, existing U32 roundtrip, strict byte codecs and parser refinement.

Final focused check: source SHA 1ea94958189f2f5b601305110dfdc24e1915c2c1ca7444989aa7b51c6bc60139, object SHA fe29617cc0428912620d04c295f5f8f4fd822784fc68085d6683f9941e31c55c, exit 0, 13.039 seconds, process RSS 3,251,617,792 bytes, zero swaps. Four axiom reports contain only standard axioms. Actual launch HEAD is f42c60008fd149e9a766cdbd3e869c269b96c682. No separate preflight file was emitted; command and launch receipt are retained, and the original stale RSS metadata is preserved under provenance with the correction recorded in manifest.json.

The eight canonicality premises remain explicit. P6-to-Rust-Std ABI, concrete compact-buffer caller integration, whole source/runtime/deployment refinement and global soundness remain open. This is not closure of the entire S5 re-pin row.
