# R435 attempt C custody audit

This read-only audit validates attempt C against its saved source, receipt, Lean log, GNU time output, launcher and copy receipts, and effective before/after cgroup snapshots. The root `R435HelperGuards.UNVERIFIED.lean` is byte-identical to C's compiled source. C preserves B's four existing definitions byte-for-byte, then adds `helper114_bounded_addresses` and `helper114_success` with two corresponding axiom-print requests.

C exited 0 in 1.32 seconds with GNU peak RSS 2,540,244 KiB and zero swaps. Its six complete axiom reports match the raw output and receipt; all list only `propext`, `Classical.choice`, and `Quot.sound`. Effective cgroup limits are 5/7 GiB, zero swap, 128 tasks, with no high/max/OOM events. GNU RSS and cgroup peak are recorded separately. All six copied-artifact status records pass.

Attempts A and B remain unchanged sibling records: A is the failed platform-width simplification attempt with `sorryAx` only in rejected output; B is the green four-report predecessor. This is a generic Lean scalar/helper fragment audit, not a native execution-closure or Rust source-correspondence claim.

Run `python3 verify_attempt_c.py` from this directory to print a fresh report. It reads but does not modify the saved attempts.
