# R419 saved-run evidence preflight

Read-only consistency audit of the saved Rust compile, test, and candidate-run receipts. No compiler, test binary, or AST transform was rerun.

All 13 saved run folders passed receipt/log metrics, source snapshot, revision, resource cap, and zero-swap checks. Pinned compiler: 1.98.0-nightly (14210df0e 2026-05-31); source revision: `3f22e765d32b16d016f4ff603d599ea72838c37a`; cap per run: 5G high / 7G max / 0 swap / 128 tasks.

The focused fixture run at `1790967562246457000` reports 18 passed tests. The first candidate at `1790967775715172000` failed before output at unique source-qualified lookup (the prefix matched 87 names); its input SHA remained unchanged. The filtered lookup candidate at `1790967913444473000` exited 0 and emitted a new LLBC file; this is recorded only as an unverified serialization candidate.

The original R396 LLBC was SHA-256 checked as `399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae`. Run-by-run receipt, raw log, and source snapshot hashes are in `manifest.json`.

Boundary: native AST helper fixtures and candidate serialization only. There is no Aeneas translation, Lean theorem, source-semantics result, or security claim. `#print axioms` is not applicable to these Rust runs.
