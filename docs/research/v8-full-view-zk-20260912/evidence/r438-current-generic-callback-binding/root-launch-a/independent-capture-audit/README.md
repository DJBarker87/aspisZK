# R438 saved capture custody audit

`audit_capture.py` is a read-only check over the saved R438 run and saved R437 baseline command. It verifies the recorded launch/collection statuses, source/toolchain/baseline hashes, exact Charon argv change, LLBC/stdout/stderr hashes, GNU time status and metrics, effective before/after cgroup caps, terminal memory peak/events/swap, and diagnostic-only metadata. It does not connect to the host or rerun extraction.

The result is PASS for 13 checks. The saved LLBC is 3,518,851 bytes, SHA-256 `76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6`, `has_errors=false`. GNU time records exit 0, 14.74 seconds, peak RSS 630,068 KiB, swap 0. The terminal cgroup reports `memory.peak=496250880`, `memory.swap.peak=0`, and zero `high`, `max`, `oom`, `oom_kill`, and `oom_group_kill` events; caps were 5 GiB high, 7 GiB max, 0 swap, 128 pids. Charon/Rust pins and exact command are in the saved run artifacts.

This audit addresses capture custody and literal LLBC/tooling facts only. It does not establish execution, source correspondence, trait dispatch, or security.
