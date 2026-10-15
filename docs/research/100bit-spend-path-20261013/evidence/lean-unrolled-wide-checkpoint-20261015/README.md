# Unrolled wide parser checkpoint evidence

This bundle records one focused NUC checkpoint target, `R1UnrolledWideParserCheckpoint`, compiled against the selected unrolled-wide refinement and its direct predecessor modules. The checkpoint printed 12 public theorem axiom reports; each reports only `propext`, `Classical.choice`, and `Quot.sound`.

The attempt exited 0 in 1.57 seconds with peak RSS 3,785,468 KiB, zero swap, and cgroup limits `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Its exact source hash is recorded as `source_sha256` in the manifest and matched both the precompile snapshot and selected local source. Each selected module records source and object hashes separately.

The deterministic object archive contains the checkpoint plus the seven selected direct proof dependencies listed in the manifest. Their source/object provenance links to the predecessor evidence bundles. This evidence records Lean compilation only; it makes no runtime adoption or source-refinement conclusion.
