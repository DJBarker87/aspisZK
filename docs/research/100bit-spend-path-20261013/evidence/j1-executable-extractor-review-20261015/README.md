# Executable trace extractor artifact review

This separate read-only audit covers the three targets in `lean-executable-trace-extractor-20261015`: `R1TraceValueDecode`, `R1ComputableTraceWitness`, and `R1TraceWitnessExtract`. It does not replace the individual module audits. No build or source edit was performed.

The source bundle has 64 recorded checksum entries; all verify. Seven attempts are preserved: four failed and three green. For each attempt, the source snapshot and sidecar match the recorded source digest, the receipt matches the source digest and exit status, and output and timing logs are present. Current worktree sources for all three final targets match their green-attempt digests. The archive SHA and all 15 object member hashes and sizes match the manifest. Across the three green targets, all seven `#print axioms` reports list only `propext`, `Classical.choice`, and `Quot.sound`.

The bundle retains an import provenance limitation: the included `R0P/Core.lean` is a historical source counterpart, while the compile used the cached `R0P.Core` object through an external object-cache symlink. The bundle does not assert source equality for that cached object. `review.json` records this limitation along with per-file pins, attempt receipts, resource data, and axiom output.

This audit validates the recorded build artifacts only. It does not assess mathematical adequacy, protocol/source refinement, or security closure.
