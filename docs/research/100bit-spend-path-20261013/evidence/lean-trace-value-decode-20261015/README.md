# Trace value decoder focused Lean evidence

This package records the single focused target R1TraceValueDecode. The decoder reads wide-trace cells 1008, 1010, and 1012, projects each into the exact M31 base field, and returns bounded 30-bit values when all three canonical representatives are below 2^30. The theorem decode_of_values establishes the result for cells equal to the embedded natural values. It assumes no production or protocol-validity premise.

The pinned NUC run completed with exit status 0 in 1.57 s, maximum RSS 3,318,116 KiB, and zero swap, under MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128. The #print axioms output for decode_of_values contains only propext, Classical.choice, and Quot.sound. The log has unused-simp-argument linter warnings; the target compiled successfully.

The attempt snapshot, receipt, sidecars, stdout, and timing log are preserved in attempts/. The deterministic object archive contains the target and its cached imported Lean objects. Source and runner pins are recorded in source-manifest.json. The cached R0P.Core object came from the pinned workspace's external object cache; the included historical source counterpart is provenance only, not asserted as the source used to build that cached object. No loose .olean files are retained.
