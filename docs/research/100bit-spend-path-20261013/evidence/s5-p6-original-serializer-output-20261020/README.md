# Original `WideExact::to_le_bytes` output under the corrected P6 model

This focused packet proves the unchanged generated serializer returns the exact ordered 32-byte little-endian representation of its eight `to_limbs` words when interpreted through the corrected explicit P6 mutable-iterator/zip model. The model writes each yielded chunk back at the captured start.

The source adapter checker reconstructs the adapted generated Funs exactly from the pinned original generated Funs by removing the two resource options and applying only three named mutable-iterator/zip interface substitutions. The generated `to_limbs`, loop body, loop wrapper and outer method body remain textually unchanged.

The checked result is conditional on the explicit P6 extraction-harness model. Rust standard-library alias/writeback and iterator ABI correspondence remain open. This packet makes no production adoption claim.

See `manifest.json` for exact pins and receipts. Some inherited owner source/object pairs have hashes but no standalone producer receipt; this is stated directly rather than inferred. The retained v21 failed proof attempt is diagnostic. Root v22 trace-stop and v23 WHNF-timeout diagnostics are also preserved and rejected; V24 avoids normalizing the concrete final iterator state by generalizing its final back continuation and applying a generic slice-content lemma. No compiled objects are included.

The selected final wrapper target passed in5.689s,process RSS2,268,938,240B,aggregate2,244,542,464B,zero swaps,with ten standard-only axiom reports. Its source revision at launch was cb0af9a36. It assumes no canonicality, internal loop-success, individual writeback-success or independently supplied serializer-output equality. Source/model/runtime boundaries listed above remain explicit.
