# R434 command and saved-capture audit

`audit_capture.py` is a read-only check of R434's launch plan and saved output against the R431 command snapshot. It confirms the extraction command is exactly the R431 command with two added helper includes (`core::ptr::const_ptr::_::offset_from_unsigned::precondition_check` and `core::num::_::unchecked_add::precondition_check`) and a fresh destination. The existing root, source hashes, baseline, Charon source/toolchain, Rust compiler, features, release mode, and other flags remain pinned.

The saved run completed successfully: Charon and GNU time exited 0, LLBC `has_errors` is false, and the output/log hashes match `result.json`. GNU time records 13.79 seconds, 630,388 KiB peak RSS, and zero swaps. The after-run reservation snapshot records the actual cgroup limits and terminal cgroup peak separately from GNU RSS; memory event counters show no high/max/OOM events. The launch and output collection both exited 0.

This is diagnostic LLBC extraction evidence only. Formal axioms are not applicable, and this audit establishes no pointer, unsafe-operation, Rust-source, or callback theorem. Run from this directory with `python3 audit_capture.py`; it prints a fresh report and does not modify saved capture files.
