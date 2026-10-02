# R396 unmonomorphized generic batch extraction

R396 is a successful Charon extraction of the same frozen batch root and LLBC source snapshot used by R327, with exactly one extraction-mode change: `--monomorphize` is omitted; output goes to the fresh R396 destination. The extraction used the frozen ordered includes, offline locked release Cargo profile with one job, saved RUSTFLAGS, pinned Charon binary, and selected `nightly-2026-06-01` compiler. The run completed with Charon exit 0 and `has_errors=false`; LLBC SHA256 is `399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae`.

The exact generic declaration `core::iter::traits::iterator::Iterator::try_fold` at `/rustc/library/core/src/iter/traits/iterator.rs:2486:4–2490:35` is present with a structured body. Its signature retains the by-value `F` parameter and original generic region, five type parameters, four trait clauses, and `Try::Output = B` associated-type constraint. The complete decoded row contains zero `Erased` region occurrences. `selected-try-fold-row.json` preserves its complete decoded row; `selected-try-fold-callees.json` records the five trait-method call sites and source method names.

`extract.log` records 13.66 seconds wall time, 623720 KiB maximum resident set size, zero swaps, and exit status 0. `host-reservation-before.json` and `host-reservation-after.json` preserve the reservation and scope records; `extract-command.json`, `launch.json`, and `toolchain.txt` preserve argv, hashes, source revision, and compiler provenance. `audit_r396.py` is a read-only saved-LLBC auditor.

This is an extraction result only. It makes no translation or Lean-proof claim and does not establish source-semantics, execution, cryptographic, or security correspondence.
