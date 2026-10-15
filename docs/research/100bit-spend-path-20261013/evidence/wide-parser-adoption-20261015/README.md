# Exact unrolled parser adoption

`adoption.json` records adoption on the research branch of the exact h2
`wide_exact.rs` bytes used by extraction, native differential tests, and the
five passing SBF settlement gates. `runtime.patch` is the actual unified diff.
Only the two parser method bodies change; their attributes and constructor
layout are preserved. The adjacent `field.rs` is unchanged.

`ROOT-VALIDATION.json` checks 893 existing evidence-index entries, selected
source/object pins, all 12 checkpoint axiom reports, capped proof receipts,
and both source-retention checkers. It records five successful unrolled
targets and eleven failed compile attempts, all retained. An additional
empty preflight snapshot is recorded separately by the limb-check bundle.

All 459 manifest-listed files under `crates/` and `programs/` were present.
Before adoption, 457 matched, the parser was the intended change, and the
remaining difference was a test file not built into the SBF program. The
full copied 751-entry historical workspace also contains research files and
build caches; this is not a claim that the entire checkout matches it.

Four earlier SBF/cost checksum indices needed path normalization. Two inline
indices also contained stale self/cross-index entries. Their original
indices and repair records are retained in their bundles; every non-index
artifact hash was checked before replacement. No raw build or test receipt
was rewritten.

This evidence proves neither extractor/compiler correctness nor complete
verifier soundness, privacy, or deployment provenance. It does not certify
100-bit non-work-normalized security.
