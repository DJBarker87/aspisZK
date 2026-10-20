# Focused R4 transport kit

`prepare.py OUT` makes a standalone Rust crate containing complete, byte-pinned
scanner bodies cut from the unchanged shipped source, followed by Kani harnesses.
It rejects a contract scanner that differs outside the single named membership
substitution. No crate/program file is modified. Generate outside the worktree.

Accepted component scopes:

- `words_and_iterator_order`: arbitrary 32-byte blocks, little-endian decoding,
  low18 mask/modulo identity, all eight by-value array visits in order.
- `finish_rejects_short_and_accepts_full`: all accepted lengths0..22.
- `prefix_contains_len_0` through `prefix_contains_len_22`: arbitrary stored
  words and candidate, full exhaustive length partition; the strengthened
  version also proves the exact Boolean contract used by the scanner cut.

The direct full scan harness timed out. The scanner with verified membership
substitution also timed out after replacing a memcmp unwind failure with explicit
word comparisons. Neither is a proof result; no assertion or unwinding check was
turned off. The kit does not claim a complete scanner-to-Lean refinement.

`extract-wide.py` is a build-host-only pinned extraction preflight for exact
optimized helper bodies. Its generated external templates are diagnostic only;
never import their axioms into an accepted Lean owner. Full paths, tool hashes,
commands, scope admission and outcomes are retained in the evidence packet.

`capped.py` must be invoked inside its own systemd scope with
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. `reservation.py`
checks populated host reservations against55GiB before another8GiB scope.
Receipts cannot be reused. Do not repeat an unchanged verification run.

The receipt commands document the actual invocations. Kani uses its own compiler
pipeline; the ordinary Rust Charon preflight uses `--release`. No dense native
arithmetic computation or frozen ELF rebuild occurs in this kit.
