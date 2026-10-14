# R1 parser limb regression

This evidence records one focused optimized Rust test of the newly added exhaustive limb-position regression in `crates/aspis-r1-cost-probe/tests/validated_prefix.rs`. The test passed (1 passed, 0 failed) on the NUC in a dedicated systemd scope capped at 4 GiB `MemoryHigh`, 6 GiB `MemoryMax`, and zero swap. It checks `parse_record` behavior for semantic rows 14 through 26; it does not establish a full protocol/source correspondence.

The isolated source snapshot was built from 506 tracked workspace files at base `d08448d3a0bcd78a777217eaa6594fc658115cc2`, plus the exact worktree diff for the test. The source manifest and archive record per-file hashes. The existing release target cache was reused from `/home/dombarker/project-offloads/aspis-r1-p2-20261010/target`; older workspace files and evidence were left unchanged.

`execution.json`, `time.log`, `cgroup-memory-peak-bytes.txt`, `cgroup-swap-current-bytes.txt`, and `out.log` retain the command, result, resource readings, and test output. GNU time process maximum RSS and cgroup aggregate peak are reported separately because they differed.
