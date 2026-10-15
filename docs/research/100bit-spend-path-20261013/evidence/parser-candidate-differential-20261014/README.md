# Candidate parser differential evidence

Attempt a failed while compiling the standalone harness because the path-attributed source modules did not resolve `wide_exact` and `alloc` was not declared. The exact failed logs and initial/final service receipts are retained.

Attempt b changed only the wrapper: it added `extern crate alloc;` and switched to ordinary `mod baseline; mod field;` so Rust resolves each module's `wide_exact.rs` sibling. The Rust field sources and test logic are otherwise byte-identical to the pinned inputs. Rustc compiled the test harness in optimized mode, and the exact single test passed 221,597 input vectors / 443,194 parser comparisons. The b command logs and GNU-time records, binary hash, and initial service receipt are retained. The root observed service completion as exit 0 in 5.389 seconds with peak RSS 295,864 KiB and no swap; the final outer tool-result JSON was not retained.

This finite differential suite is evidence about those sampled cases only. It does not establish full parser equivalence. All source files, commands, logs, run metadata, and the test binary are recorded in the attempt archives and manifest.
