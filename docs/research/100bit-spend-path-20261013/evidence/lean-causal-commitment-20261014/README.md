# Causal commitment recovery evidence

This bundle records focused Lean compilation evidence for a finite-table recovery model with full-trace hash events. The model treats the actual oracle trace as a prefix and suffix, retaining intervening reads in the trace and first-read accounting. The C1, C2, and folded-root specializations use the corresponding fixed-width leaf encodings and commitment-root records.

The final checkpoint imports the C1 and later-commitment stability, combined Merkle collision, index geometry, and recorded-root modules, then prints 14 public axiom reports. The earlier common-trace checkpoint is separately archived. The successful target sources and objects are identified by SHA-256 in `source-manifest.json`; every recorded attempt and exact source snapshot is retained. There were 41 attempts: 24 failures and 17 final green attempts, with no superseded green attempts. All successful attempts together printed 77 axiom reports. The final checkpoint used the pinned NUC runner with `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`.

The results establish only the statements in the archived Lean sources under their listed premises. They do not establish correspondence between the Lean model and Rust execution, a complete protocol security theorem, or a concrete attack bound.
