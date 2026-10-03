# R433 saved compilation custody audit

This read-only audit checks the saved R433 attempt B compilation against its own source, raw compiler log, GNU time output, launch and copy receipts, and before/after cgroup snapshots. It confirms that `R433ConstructorFragment.UNVERIFIED.lean` is byte-identical to `attempt-b/source.lean`; the successful target is `AspisV8R19/R433ConstructorFragment.lean`.

Attempt B exited 0 with four complete axiom reports. `constructor86` reports no axioms; the other three reports list only `propext`, `Classical.choice`, and `Quot.sound`. The source and receipt agree on Lean 4.32.0, source revision, wall time, RSS, and zero swap. Effective cgroup limits and memory events are checked independently from GNU time. Attempt A is retained as a failed termination proof; its `sorryAx` output is rejected history and is not counted as a successful result.

This records compilation custody for the generic constructor/pointer fragment model. It does not prove Rust source correspondence, pointer lifetime or alias behavior, or the complete callback.

Run from this directory with `python3 verify_attempt_b.py`; the script reads the adjacent saved attempts and prints a fresh report without modifying them. `SHA256SUMS` covers this audit's own files.
