# Unified causal first-hit adapter evidence

This bundle records three focused attempts for `R1UnifiedCausalBound`. Attempts `a` and `b` preserve initial elaboration failures; attempt `c` is green (exit 0, 1.68 s, 3,536,320 KiB peak RSS, zero swap) under the pinned 4 GiB high / 6 GiB max / zero-swap runner.

The module applies the existing R0C.V3 `lemmaA3` to the unified background decoder after `UnifiedDecoderBound.decoded_bound` transfers a uniform independent-mean premise for each fixed row and prefix. The companion result derives the pathwise first-read bound from a distinct-first-read cap and converts the lazy mean to the empty-oracle mean. Both results remain conditional on the stated density premise; this package contains no concrete bad-event bound or acceptance-to-hit/extraction result.

`source-manifest.json` pins the pre-edit source revision, final source and object hashes, all attempt receipts/snapshots/logs, runner files, and direct imported source files. `objects/R1UnifiedCausalBound.tar.gz` contains the single final object.
